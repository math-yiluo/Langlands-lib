import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Gluing sections of an fppf sheaf along an open cover

Sections of an fppf sheaf on the open subschemes of a Zariski cover of a scheme over `S`, which
agree on the pairwise intersections, glue to a section on the whole scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

variable {S : Scheme.{u}}

/-- An open subscheme of a scheme over `S`, as a scheme over `S`. -/
abbrev openOver (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of an open subscheme, as a morphism over `S`. -/
abbrev openOverι (T : Over S) (U : T.left.Opens) : openOver T U ⟶ T :=
  Over.homMk U.ι

/-- The inclusion of a smaller open subscheme into a larger one, over `S`. -/
abbrev openOverHomOfLE (T : Over S) {U V : T.left.Opens} (h : U ≤ V) :
    openOver T U ⟶ openOver T V :=
  Over.homMk (T.left.homOfLE h) (by simp [Scheme.homOfLE_ι_assoc])

@[reassoc (attr := simp)]
theorem openOverHomOfLE_ι (T : Over S) {U V : T.left.Opens} (h : U ≤ V) :
    openOverHomOfLE T h ≫ openOverι T V = openOverι T U := by
  apply Over.OverMorphism.ext
  simp

/-- An open cover of a scheme over `S` is an fppf covering family. -/
theorem openOver_covering {ι : Type*} (T : Over S) (U : ι → T.left.Opens)
    (hU : TopologicalSpace.IsOpenCover U) :
    Sieve.ofArrows (fun i => openOver T (U i)) (fun i => openOverι T (U i)) ∈
      fppfTopology S T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono
    Scheme.zariskiPrecoverage_le_fppfPrecoverage) _
      (T.left.openCoverOfIsOpenCover U hU).mem_grothendieckTopology

/-- Two morphisms into members of an open cover with the same composite to the whole scheme
factor through the intersection. -/
theorem exists_inf_lift (T : Over S) {U V : T.left.Opens} {Z : Over S}
    (g : Z ⟶ openOver T U) (h : Z ⟶ openOver T V)
    (w : g ≫ openOverι T U = h ≫ openOverι T V) :
    ∃ c : Z ⟶ openOver T (U ⊓ V), c ≫ openOverHomOfLE T inf_le_left = g ∧
      c ≫ openOverHomOfLE T inf_le_right = h := by
  have w' : g.left ≫ U.ι = h.left ≫ V.ι := congrArg CommaMorphism.left w
  have hr : Set.range (g.left ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · change (g.left ≫ U.ι) z ∈ (U : Set T.left)
      rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    · change (g.left ≫ U.ι) z ∈ (V : Set T.left)
      rw [w', Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
  let c₀ : Z.left ⟶ (U ⊓ V : T.left.Opens) := IsOpenImmersion.lift (U ⊓ V).ι _ hr
  have hc₀ : c₀ ≫ (U ⊓ V).ι = g.left ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have hZ : c₀ ≫ (U ⊓ V).ι ≫ T.hom = Z.hom := by
    rw [← Category.assoc, hc₀, Category.assoc]
    exact Over.w g
  refine ⟨Over.homMk c₀ hZ, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← cancel_mono U.ι]
    simp [hc₀]
  · apply Over.OverMorphism.ext
    rw [← cancel_mono V.ι]
    simp [hc₀, w']

/-- Sections of an fppf sheaf over the members of an open cover that agree on pairwise
intersections glue to a section over the whole scheme. -/
theorem exists_glue (F : FppfSheaf S) {ι : Type*} (T : Over S) (U : ι → T.left.Opens)
    (hU : TopologicalSpace.IsOpenCover U) (x : ∀ i, F.obj.obj (op (openOver T (U i))))
    (hx : ∀ i j, F.obj.map (openOverHomOfLE T (inf_le_left : U i ⊓ U j ≤ U i)).op (x i) =
      F.obj.map (openOverHomOfLE T (inf_le_right : U i ⊓ U j ≤ U j)).op (x j)) :
    ∃ y : F.obj.obj (op T), ∀ i, F.obj.map (openOverι T (U i)).op y = x i := by
  have hsh := (isSheaf_iff_isSheaf_of_type (fppfTopology S) F.obj).mp F.property
  have ha := (Presieve.isSheafFor_arrows_iff F.obj (fun i => openOverι T (U i))).mp
    ((Presieve.isSheafFor_iff_generate (P := F.obj) (Presieve.ofArrows _ _)).mpr
      (hsh _ (openOver_covering T U hU)))
  obtain ⟨y, hy, -⟩ := ha x (by
    intro i j Z g h w
    obtain ⟨c, hc₁, hc₂⟩ := exists_inf_lift T g h w
    rw [← hc₁, ← hc₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hx])
  exact ⟨y, hy⟩

/-- Opens `U i ≤ V` whose union is `V` form an fppf covering family of the open subscheme `V`. -/
theorem openOver_covering_le {ι : Type*} (T : Over S) (V : T.left.Opens) (U : ι → T.left.Opens)
    (hle : ∀ i, U i ≤ V) (hU : ⨆ i, U i = V) :
    Sieve.ofArrows (fun i => openOver T (U i)) (fun i => openOverHomOfLE T (hle i)) ∈
      fppfTopology S (openOver T V) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let 𝒰 : (V : Scheme.{u}).OpenCover := Scheme.Cover.mkOfCovers ι (fun i => (U i).toScheme)
    (fun i => T.left.homOfLE (hle i)) (by
      rintro ⟨x, hx⟩
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, ⟨x, hi⟩, Scheme.homOfLE_apply' _ x hi⟩)
  exact (Precoverage.toGrothendieck_mono
    Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology

/-- Sections of an fppf sheaf over opens `U i` covering an open `V`, which agree on pairwise
intersections, glue to a section over `V`. -/
theorem exists_glue_le (F : FppfSheaf S) {ι : Type*} (T : Over S) (V : T.left.Opens)
    (U : ι → T.left.Opens) (hle : ∀ i, U i ≤ V) (hU : ⨆ i, U i = V)
    (x : ∀ i, F.obj.obj (op (openOver T (U i))))
    (hx : ∀ i j, F.obj.map (openOverHomOfLE T (inf_le_left : U i ⊓ U j ≤ U i)).op (x i) =
      F.obj.map (openOverHomOfLE T (inf_le_right : U i ⊓ U j ≤ U j)).op (x j)) :
    ∃ y : F.obj.obj (op (openOver T V)), ∀ i, F.obj.map (openOverHomOfLE T (hle i)).op y = x i := by
  have hsh := (isSheaf_iff_isSheaf_of_type (fppfTopology S) F.obj).mp F.property
  have ha := (Presieve.isSheafFor_arrows_iff F.obj (fun i => openOverHomOfLE T (hle i))).mp
    ((Presieve.isSheafFor_iff_generate (P := F.obj) (Presieve.ofArrows _ _)).mpr
      (hsh _ (openOver_covering_le T V U hle hU)))
  obtain ⟨y, hy, -⟩ := ha x (by
    intro i j Z g h w
    have w' : g ≫ openOverι T (U i) = h ≫ openOverι T (U j) := by
      rw [← openOverHomOfLE_ι T (hle i), ← openOverHomOfLE_ι T (hle j), reassoc_of% w]
    obtain ⟨c, hc₁, hc₂⟩ := exists_inf_lift T g h w'
    rw [← hc₁, ← hc₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hx])
  exact ⟨y, hy⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
