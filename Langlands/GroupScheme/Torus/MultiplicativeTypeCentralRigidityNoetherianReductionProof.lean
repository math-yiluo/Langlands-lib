import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityNoetherianReductionStatement
import Langlands.GroupScheme.HopfFiberCentralityResidue
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Proof: central rigidity for groups of finite presentation from the noetherian case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralRigidityNoetherianReduction

open Descent HopfFiberCentralityResidue RelativeMultiplicativeType

section Transfer

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The fibre hypotheses of SGA 3, IX, Théorème 5.1 at a point `s`: the fibres of `u` and
`v` at `s` agree and the fibre of `u` is central. -/
def FibreHyp (u v : H ⟶ G) (s : S) : Prop :=
  (baseChange (S.fromSpecResidueField s)).map u =
      (baseChange (S.fromSpecResidueField s)).map v ∧
    IsCentral ((baseChange (S.fromSpecResidueField s)).map u)

/-- The conclusion of SGA 3, IX, Théorème 5.1 at a point `s`: `u` and `v` agree over an open
neighbourhood of `s`. -/
def LocalEq (u v : H ⟶ G) (s : S) : Prop :=
  ∃ U : S.Opens, s ∈ U ∧ (baseChange U.ι).map u = (baseChange U.ι).map v

/-- Base change along a flat surjective morphism is faithful on homomorphisms. -/
theorem baseChange_map_injective {S' : Scheme.{u}} (b : S' ⟶ S) [Flat b] [Surjective b]
    {u v : H ⟶ G} (h : (baseChange b).map u = (baseChange b).map v) : u = v := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have : Flat (pullback.fst H.X.hom b) := inferInstance
  have : Surjective (pullback.fst H.X.hom b) := inferInstance
  have : Epi (pullback.fst H.X.hom b) := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (pullback.fst H.X.hom b)).mp
  have h1 := congrArg (fun w => w.hom.hom.left ≫ pullback.fst G.X.hom b) h
  have hu : ((baseChange b).map u).hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom b ≫ u.hom.hom.left := pullback.lift_fst _ _ _
  have hv : ((baseChange b).map v).hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom b ≫ v.hom.hom.left := pullback.lift_fst _ _ _
  simp only at h1
  exact hu.symm.trans (h1.trans hv)

/-- Equality after base change along a composite is equality after the iterated base
change. -/
theorem map_eq_comp_iff {S' S'' : Scheme.{u}} (a : S' ⟶ S) (b : S'' ⟶ S') (u v : H ⟶ G) :
    (baseChange (b ≫ a)).map u = (baseChange (b ≫ a)).map v ↔
      (baseChange b).map ((baseChange a).map u) =
        (baseChange b).map ((baseChange a).map v) := by
  have hu := pullbackComparison_naturality a b (b ≫ a) rfl u
  have hv := pullbackComparison_naturality a b (b ≫ a) rfl v
  constructor
  · intro h
    rw [← cancel_mono (pullbackComparison a b (b ≫ a) rfl G).hom, hu, hv, h]
  · intro h
    rw [← cancel_epi (pullbackComparison a b (b ≫ a) rfl H).hom, ← hu, ← hv, h]

/-- Conjugating by isomorphisms preserves the fibre hypotheses. -/
theorem FibreHyp.conj {H' G' : GroupScheme S} (eH : H ≅ H') (eG : G ≅ G') {u v : H ⟶ G}
    {s : S} (h : FibreHyp u v s) : FibreHyp (eH.inv ≫ u ≫ eG.hom) (eH.inv ≫ v ≫ eG.hom) s := by
  obtain ⟨heq, hc⟩ := h
  refine ⟨by simp only [Functor.map_comp, heq], ?_⟩
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
  exact ((hc.comp _).comp_iso ((baseChange (S.fromSpecResidueField s)).mapIso eG))

/-- Local equality of the conjugates gives local equality. -/
theorem LocalEq.of_conj {H' G' : GroupScheme S} (eH : H ≅ H') (eG : G ≅ G') {u v : H ⟶ G}
    {s : S} (h : LocalEq (eH.inv ≫ u ≫ eG.hom) (eH.inv ≫ v ≫ eG.hom) s) : LocalEq u v s := by
  obtain ⟨U, hs, hU⟩ := h
  refine ⟨U, hs, ?_⟩
  have h1 := congrArg (fun w => (baseChange U.ι).map eH.hom ≫ w ≫ (baseChange U.ι).map eG.inv) hU
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    Category.id_comp] at h1
  simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Category.comp_id] using h1

/-- The morphism of spectra of residue fields induced by a morphism of schemes is flat and
surjective. -/
theorem flat_surjective_specMap_residueFieldMap {S' : Scheme.{u}} (f : S' ⟶ S) (t : S') :
    Flat (Spec.map (f.residueFieldMap t)) ∧ Surjective (Spec.map (f.residueFieldMap t)) := by
  let := (f.residueFieldMap t).hom.toAlgebra
  obtain ⟨h1, h2, -⟩ := fieldExtension_fpqc (S.residueField (f.base t)) (S'.residueField t)
  exact ⟨h2, h1⟩

/-- The fibre hypotheses are stable under base change. -/
theorem FibreHyp.pull {S' : Scheme.{u}} (f : S' ⟶ S) {u v : H ⟶ G} (t : S')
    (h : FibreHyp u v (f.base t)) :
    FibreHyp ((baseChange f).map u) ((baseChange f).map v) t := by
  obtain ⟨heq, hc⟩ := h
  have hsq := f.SpecMap_residueFieldMap_fromSpecResidueField t
  constructor
  · rw [← map_eq_comp_iff, ← hsq, map_eq_comp_iff, heq]
  · rw [← isCentral_baseChange_comp_iff, ← hsq, isCentral_baseChange_comp_iff]
    exact hc.baseChange _

/-- The fibre hypotheses descend along any morphism, since a field extension is faithfully
flat. -/
theorem FibreHyp.descend {S' : Scheme.{u}} (f : S' ⟶ S) {u v : H ⟶ G} (t : S')
    (h : FibreHyp ((baseChange f).map u) ((baseChange f).map v) t) :
    FibreHyp u v (f.base t) := by
  obtain ⟨heq, hc⟩ := h
  obtain ⟨hfl, hsu⟩ := flat_surjective_specMap_residueFieldMap f t
  have hsq := f.SpecMap_residueFieldMap_fromSpecResidueField t
  rw [← map_eq_comp_iff, ← hsq, map_eq_comp_iff] at heq
  rw [← isCentral_baseChange_comp_iff, ← hsq, isCentral_baseChange_comp_iff] at hc
  exact ⟨baseChange_map_injective _ heq, IsCentral.of_baseChange _ hc⟩

/-- Local equality is stable under base change. -/
theorem LocalEq.pull {S' : Scheme.{u}} (f : S' ⟶ S) {u v : H ⟶ G} (t : S')
    (h : LocalEq u v (f.base t)) :
    LocalEq ((baseChange f).map u) ((baseChange f).map v) t := by
  obtain ⟨U, hs, hU⟩ := h
  refine ⟨f ⁻¹ᵁ U, hs, ?_⟩
  rw [← map_eq_comp_iff, ← morphismRestrict_ι, map_eq_comp_iff, hU]

/-- Local equality descends along flat morphisms locally of finite presentation, whose images
of open subsets are open. -/
theorem LocalEq.descend {S' : Scheme.{u}} (f : S' ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {u v : H ⟶ G} (t : S')
    (h : LocalEq ((baseChange f).map u) ((baseChange f).map v) t) :
    LocalEq u v (f.base t) := by
  obtain ⟨U', ht, hU'⟩ := h
  let V : S.Opens := ⟨f.base '' U', f.isOpenMap _ U'.isOpen⟩
  have hle : U' ≤ f ⁻¹ᵁ V := fun x hx => ⟨x, hx, rfl⟩
  let g : (U' : Scheme) ⟶ V := f.resLE V U' hle
  have hg : g ≫ V.ι = U'.ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  have : Surjective g := by
    constructor
    rintro ⟨y, x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    have := congrArg (fun k => k.base ⟨x, hx⟩) hg
    exact this
  refine ⟨V, ⟨t, ht, rfl⟩, ?_⟩
  apply baseChange_map_injective g
  rw [← map_eq_comp_iff, hg, map_eq_comp_iff, hU']

end Transfer

section Model

/-- The hypothesis of the reduction: SGA 3, IX, Théorème 5.1 over locally noetherian bases,
phrased with `FibreHyp` and `LocalEq`. -/
def NoetherianHyp : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsLocallyNoetherian S → IsMultiplicativeType H →
    ∀ (u v : H ⟶ G) (s : S), FibreHyp u v s → LocalEq u v s

/-- Transfer along a model: if `u, v` over `S` are, up to isomorphisms, the base changes along
`φ : S ⟶ S₀` of `u₀, v₀`, then the fibre hypotheses for `u, v` at `s` give those for `u₀, v₀`
at `φ s`, and local equality of `u₀, v₀` at `φ s` gives local equality of `u, v` at `s`. -/
theorem model_transfer {S S₀ : Scheme.{u}} (φ : S ⟶ S₀) {H G : GroupScheme S}
    {H₀ G₀ : GroupScheme S₀} (eH : (baseChange φ).obj H₀ ≅ H) (eG : (baseChange φ).obj G₀ ≅ G)
    {u v : H ⟶ G} {u₀ v₀ : H₀ ⟶ G₀} (hu : (baseChange φ).map u₀ = eH.hom ≫ u ≫ eG.inv)
    (hv : (baseChange φ).map v₀ = eH.hom ≫ v ≫ eG.inv) (s : S) (h : FibreHyp u v s)
    (hloc : FibreHyp u₀ v₀ (φ.base s) → LocalEq u₀ v₀ (φ.base s)) : LocalEq u v s := by
  have h1 : FibreHyp ((baseChange φ).map u₀) ((baseChange φ).map v₀) s := by
    rw [hu, hv]
    exact FibreHyp.conj eH.symm eG.symm h
  have h2 := LocalEq.pull φ s (hloc (FibreHyp.descend φ s h1))
  rw [hu, hv] at h2
  exact LocalEq.of_conj eH.symm eG.symm h2

/-- A finitely generated algebra over a noetherian ring is noetherian. -/
theorem isNoetherianRing_of_fg {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] {T : Subalgebra R A} (hT : T.FG) : IsNoetherianRing T := by
  have := (Subalgebra.fg_iff_finiteType T).mp hT
  exact Algebra.FiniteType.isNoetherianRing R T

end Model

section Affine

variable (hyp : NoetherianHyp.{u})
include hyp

/-- The affine case over a model: `u, v` are homomorphisms between base changes along
`Spec A ⟶ Spec R` from a noetherian ring `R`. Both are descended to a finitely generated
`R`-subalgebra `T₄` of `A` (first `u`, then `v`), where the noetherian hypothesis applies. -/
theorem spec_core {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R]
    {H₀ G₀ : GroupScheme (Spec (CommRingCat.of R))} (hH₀ : IsMultiplicativeType H₀)
    [QuasiCompact H₀.X.hom] [QuasiSeparated H₀.X.hom] [LocallyOfFinitePresentation G₀.X.hom]
    (u v : (baseChange (Spec.algebraMap R A)).obj H₀ ⟶ (baseChange (Spec.algebraMap R A)).obj G₀)
    (s : Spec (CommRingCat.of A)) (h : FibreHyp u v s) : LocalEq u v s := by
  obtain ⟨T₃, hT₃, -, g₃, hg₃⟩ := FiniteCoefficient.homGeneral R A H₀ G₀ u ∅
  have : IsNoetherianRing T₃ := isNoetherianRing_of_fg hT₃
  have h₃ : Spec.algebraMap T₃ A ≫ Spec.algebraMap R T₃ = Spec.algebraMap R A := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  let cH := pullbackComparison (Spec.algebraMap R T₃) (Spec.algebraMap T₃ A)
    (Spec.algebraMap R A) h₃ H₀
  let cG := pullbackComparison (Spec.algebraMap R T₃) (Spec.algebraMap T₃ A)
    (Spec.algebraMap R A) h₃ G₀
  let H₁ := (baseChange (Spec.algebraMap R T₃)).obj H₀
  let G₁ := (baseChange (Spec.algebraMap R T₃)).obj G₀
  have : QuasiCompact H₁.X.hom := by
    change QuasiCompact (pullback.snd _ _); infer_instance
  have : QuasiSeparated H₁.X.hom := by
    change QuasiSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFinitePresentation G₁.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _); infer_instance
  obtain ⟨T₄, hT₄, -, g₄, hg₄⟩ :=
    FiniteCoefficient.homGeneral T₃ A H₁ G₁ (cH.hom ≫ v ≫ cG.inv) ∅
  have : IsNoetherianRing T₄ := isNoetherianRing_of_fg hT₄
  have h₄ : Spec.algebraMap T₄ A ≫ Spec.algebraMap T₃ T₄ = Spec.algebraMap T₃ A := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  let dH := pullbackComparison (Spec.algebraMap T₃ T₄) (Spec.algebraMap T₄ A)
    (Spec.algebraMap T₃ A) h₄ H₁
  let dG := pullbackComparison (Spec.algebraMap T₃ T₄) (Spec.algebraMap T₄ A)
    (Spec.algebraMap T₃ A) h₄ G₁
  have hn := pullbackComparison_naturality (Spec.algebraMap T₃ T₄) (Spec.algebraMap T₄ A)
    (Spec.algebraMap T₃ A) h₄ g₃
  refine model_transfer (Spec.algebraMap T₄ A) (dH ≪≫ cH) (dG ≪≫ cG)
    (u₀ := (baseChange (Spec.algebraMap T₃ T₄)).map g₃) (v₀ := g₄) ?_ ?_ s h ?_
  · simp only [Iso.trans_hom, Iso.trans_inv, ← Category.assoc]
    rw [Iso.eq_comp_inv]
    refine hn.trans ?_
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact hg₃
  · simp only [Iso.trans_hom, Iso.trans_inv, ← Category.assoc]
    rw [Iso.eq_comp_inv]
    refine hg₄.trans ?_
    simp only [Category.assoc]
    rfl
  · exact hyp _ _ _ inferInstance ((hH₀.baseChange _).baseChange _) _ _ _

/-- The affine case: over `Spec A`, with `H` diagonalizable and `G` of finite presentation.
`G` descends to a group `G₀` over a finitely generated `ℤ`-subalgebra `T₂` of `A`, and `H` is
the base change of the diagonalizable group over `Spec T₂`. -/
theorem spec_case {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (hH : IsDiagonalizable H) [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] {u v : H ⟶ G} (s : Spec R)
    (h : FibreHyp u v s) : LocalEq u v s := by
  obtain ⟨A, _, rfl⟩ : ∃ (A : Type u) (_ : CommRing A), CommRingCat.of A = R := ⟨R, _, rfl⟩
  obtain ⟨Λ, _, hΛ, ⟨eH⟩⟩ := hH
  have : IsNoetherianRing (⊥ : Subalgebra ℤ A) := isNoetherianRing_of_fg Subalgebra.fg_bot
  obtain ⟨T₁, hT₁, -, X₀, f₀, π, _, _, _, hπ⟩ :=
    AlgebraicGeometry.NoetherianApproximation.schemeSubalgebraDescent
      (A₀ := (⊥ : Subalgebra ℤ A)) G.X.hom ∅
  have : IsNoetherianRing T₁ := isNoetherianRing_of_fg hT₁
  obtain ⟨T₂, hT₂, -, G₀, a₀, ha₀, -, ⟨eG⟩⟩ := subalgebraDescent f₀ G π hπ ∅
  have : IsNoetherianRing T₂ := isNoetherianRing_of_fg hT₂
  have : LocallyOfFinitePresentation G₀.X.hom := MorphismProperty.of_isPullback ha₀ ‹_›
  have : IsAffineHom (diagonalizable (Spec (CommRingCat.of T₂)) Λ).X.hom :=
    isAffineHom_diagonalizable _ Λ
  let eH' : H ≅ (baseChange (Spec.algebraMap T₂ A)).obj
      (diagonalizable (Spec (CommRingCat.of T₂)) Λ) :=
    eH ≪≫ (diagonalizableBaseChangeIso _ Λ).symm
  exact LocalEq.of_conj eH' eG (spec_core hyp
    (IsMultiplicativeType.of_isDiagonalizable ⟨Λ, _, hΛ, ⟨Iso.refl _⟩⟩) _ _ s
    (FibreHyp.conj eH' eG h))

end Affine

end Langlands.GroupScheme.CentralRigidityNoetherianReduction

namespace Langlands.GroupScheme

open CentralRigidityNoetherianReduction RelativeMultiplicativeType

/-- **Reduction of SGA 3, IX, Théorème 5.1 b) to the locally noetherian case**: if the
conclusion holds over every locally noetherian base, it holds over any base for groups `G` of
finite presentation. -/
theorem multiplicativeTypeCentralRigidityNoetherianReduction :
    MultiplicativeTypeCentralRigidityNoetherianReductionStatement.{u} := by
  intro hyp S H G hH _ _ _ u v s hs hc
  have hyp' : NoetherianHyp.{u} := fun S H G hS hH u v s h => hyp S H G hS hH u v s h.1 h.2
  obtain ⟨𝒰, h𝒰⟩ := hH
  obtain ⟨i, t, rfl⟩ := 𝒰.exists_eq s
  have : Flat (𝒰.f i) := (𝒰.map_prop i).1
  have : LocallyOfFinitePresentation (𝒰.f i) := (𝒰.map_prop i).2
  let 𝒱 := (𝒰.X i).affineOpenCover
  obtain ⟨w, hw⟩ := 𝒱.covers t
  let a := 𝒱.f (𝒱.idx t)
  let f := a ≫ 𝒰.f i
  have hft : f.base w = (𝒰.f i).base t := by
    simp only [f, a, Scheme.Hom.comp_base, TopCat.comp_app, hw]
  have hD : IsDiagonalizable ((baseChange f).obj H) :=
    IsDiagonalizable.of_iso (Descent.pullbackComparison (𝒰.f i) a f rfl H).symm
      ((h𝒰 i).baseChange a)
  have : LocallyOfFinitePresentation ((baseChange f).obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd _ _); infer_instance
  have : QuasiCompact ((baseChange f).obj G).X.hom := by
    change QuasiCompact (pullback.snd _ _); infer_instance
  have : QuasiSeparated ((baseChange f).obj G).X.hom := by
    change QuasiSeparated (pullback.snd _ _); infer_instance
  have hF : FibreHyp u v (f.base w) := by rw [hft]; exact ⟨hs, hc⟩
  have := LocalEq.descend f w (spec_case hyp' hD w (FibreHyp.pull f w hF))
  rw [hft] at this
  exact this

end Langlands.GroupScheme
