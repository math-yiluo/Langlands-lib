import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDiagonal
import Mathlib.CategoryTheory.Sites.Over

/-! # Equality of sections on the full slice over their test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {F : Presheaf S} {T : Over S}

/-- The structural map of a test over `T`, viewed over the original base. -/
def sectionTestMap (U : Over T.left) : (Over.map T.hom).obj U ⟶ T :=
  Over.homMk U.hom

@[reassoc (attr := simp)]
theorem sectionTestMap_natural {U V : Over T.left} (a : U ⟶ V) :
    (Over.map T.hom).map a ≫ sectionTestMap V = sectionTestMap U := by
  ext
  exact Over.w a

/-- The equality locus on the full slice over the scheme carrying two sections. -/
def sectionEqualizerSubfunctor (x y : F.obj (op T)) :
    Subfunctor ((schemeYoneda T.left).obj (Over.mk (𝟙 T.left))) where
  obj U := fun _ ↦ F.map (sectionTestMap U.unop).op x =
    F.map (sectionTestMap U.unop).op y
  map {U V} a _ h := by
    change F.map (sectionTestMap V.unop).op x = F.map (sectionTestMap V.unop).op y
    rw [← sectionTestMap_natural a.unop, op_comp, F.map_comp_apply, F.map_comp_apply, h]

/-- A subterminal presheaf recording where the two sections agree. -/
def sectionEqualizer (x y : F.obj (op T)) : Presheaf T.left :=
  (sectionEqualizerSubfunctor x y).toFunctor

instance sectionEqualizer_obj_subsingleton (x y : F.obj (op T)) (U : (Over T.left)ᵒᵖ) :
    Subsingleton ((sectionEqualizer x y).obj U) := by
  constructor
  intro a b
  apply Subtype.ext
  apply ULift.ext
  exact Over.mkIdTerminal.hom_ext _ _

/-- Equality of sections of a sheaf is a sheaf condition on all schemes over `T`. -/
theorem isSheaf_sectionEqualizer (hF : Presheaf.IsSheaf (fppfTopology S) F)
    (x y : F.obj (op T)) :
    Presheaf.IsSheaf (fppfTopology T.left) (sectionEqualizer x y) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  rw [sectionEqualizer, Subfunctor.isSheaf_iff _ (KernelPair.isSheaf_schemeYoneda _)]
  intro U s hs
  let Q : FppfSheaf S := ⟨F, hF⟩
  have hQ := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) T.hom).obj Q).property
  apply (hQ.isSeparated _ hs).ext
  intro V a ha
  change F.map ((Over.map T.hom).map a).op (F.map (sectionTestMap U.unop).op x) =
    F.map ((Over.map T.hom).map a).op (F.map (sectionTestMap U.unop).op y)
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, sectionTestMap_natural]
  exact ha

/-- A subterminal full presheaf is the equality locus once its inhabitation
criterion is equality of the restricted sections. -/
def sectionEqualizerIsoOfIff (x y : F.obj (op T)) (G : Presheaf T.left)
    (hG : ∀ U, Subsingleton (G.obj U))
    (h : ∀ U : Over T.left, Nonempty (G.obj (op U)) ↔
      F.map (sectionTestMap U).op x = F.map (sectionTestMap U).op y) :
    G ≅ sectionEqualizer x y where
  hom :=
    { app U := ↾fun a ↦ ⟨⟨Over.homMk U.unop.hom (by simp)⟩, (h U.unop).1 ⟨a⟩⟩
      naturality := by
        intro U V a
        ext z
        exact Subsingleton.elim _ _ }
  inv :=
    { app U := ↾fun a ↦ Classical.choice ((h U.unop).2 a.2)
      naturality := by
        intro U V a
        ext z
        exact (hG V).elim _ _ }
  hom_inv_id := by
    ext U z
    exact (hG U).elim _ _
  inv_hom_id := by
    ext U z
    exact Subsingleton.elim _ _

/-- Equality loci commute with arbitrary restriction of the scheme carrying
the two sections. -/
def sectionEqualizerRestrictIso (x y : F.obj (op T)) {U : Scheme.{u}} (j : U ⟶ T.left) :
    (Over.map j).op ⋙ sectionEqualizer x y ≅
      sectionEqualizer
        (F.map (Over.homMk j : Over.mk (j ≫ T.hom) ⟶ T).op x)
        (F.map (Over.homMk j : Over.mk (j ≫ T.hom) ⟶ T).op y) := by
  let T' : Over S := Over.mk (j ≫ T.hom)
  let k : T' ⟶ T := Over.homMk j
  refine sectionEqualizerIsoOfIff (T := T') (F.map k.op x) (F.map k.op y)
    ((Over.map j).op ⋙ sectionEqualizer x y)
    (fun V ↦ sectionEqualizer_obj_subsingleton x y ((Over.map j).op.obj V)) ?_
  intro V
  have hw : sectionTestMap (T := T') V ≫ k =
      sectionTestMap ((Over.map j).obj V) := by
    ext
    rfl
  change Nonempty ((sectionEqualizer x y).obj (op ((Over.map j).obj V))) ↔
    F.map (sectionTestMap V).op (F.map k.op x) =
      F.map (sectionTestMap V).op (F.map k.op y)
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, hw]
  exact ⟨fun ⟨a⟩ ↦ a.2,
    fun h ↦ ⟨⟨⟨Over.homMk ((Over.map j).obj V).hom (by simp)⟩, h⟩⟩⟩

/-- A represented equality locus is subterminal over the test scheme. -/
theorem mono_of_sectionEqualizerIso (x y : F.obj (op T)) (W : Over T.left)
    (e : (schemeYoneda T.left).obj W ≅ sectionEqualizer x y) : Mono W.hom := by
  constructor
  intro U a b hab
  let U' : Over T.left := Over.mk (a ≫ W.hom)
  let a' : U' ⟶ W := Over.homMk a
  let b' : U' ⟶ W := Over.homMk b hab.symm
  have he : e.hom.app (op U') ⟨a'⟩ = e.hom.app (op U') ⟨b'⟩ :=
    Subsingleton.elim _ _
  have he' := (ConcreteCategory.bijective_of_isIso (e.hom.app (op U'))).injective he
  exact congrArg (fun z ↦ z.down.left) he'

/-- A full-slice representation cuts out the original equalizer over the
original base, with a monomorphic represented projection. -/
theorem representsEqualizer_of_sectionEqualizerIso (x y : F.obj (op T))
    (W : Over T.left) (e : (schemeYoneda T.left).obj W ≅ sectionEqualizer x y) :
    Mono (sectionTestMap (T := T) W).left ∧
      RepresentsEqualizer (sectionTestMap (T := T) W) x y := by
  refine ⟨mono_of_sectionEqualizerIso x y W e, ?_⟩
  intro U g
  let U' : Over T.left := Over.mk g.left
  let d : (Over.map T.hom).obj U' ≅ U :=
    Over.isoMk (Iso.refl _) (by simp [U'])
  have hw : d.hom ≫ g = sectionTestMap U' := by
    ext
    simp [d, U', sectionTestMap]
  have hiff : F.map (sectionTestMap U').op x = F.map (sectionTestMap U').op y ↔
      F.map g.op x = F.map g.op y := by
    rw [← hw, op_comp, F.map_comp_apply, F.map_comp_apply]
    exact (ConcreteCategory.bijective_of_isIso (F.map d.hom.op)).injective.eq_iff
  constructor
  · rintro ⟨z, hz⟩
    let z' : U' ⟶ W := Over.homMk z.left (congrArg Over.Hom.left hz)
    exact hiff.1 (e.hom.app (op U') ⟨z'⟩).2
  · intro hxy
    let a : (sectionEqualizer x y).obj (op U') :=
      ⟨⟨Over.homMk U'.hom (by simp)⟩, hiff.2 hxy⟩
    let z' : U' ⟶ W := (e.inv.app (op U') a).down
    refine ⟨d.inv ≫ (Over.map T.hom).map z', ?_⟩
    apply Over.OverMorphism.ext
    change (𝟙 _ ≫ z'.left) ≫ W.hom = g.left
    simp [U']

end Langlands.AlgebraicGeometry.AlgebraicSpace
