import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Naturality of iterated base change and transport of morphism properties -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S)

/-- The iterated-base-change comparison is natural in algebraic spaces and their maps. -/
def baseChangeCompNatIso (w : h ≫ g = k) :
    baseChangeFunctor g ⋙ baseChangeFunctor h ≅ baseChangeFunctor k :=
  NatIso.ofComponents (BaseChangeComparison.compIso g h k w) (by
    intro X Y f
    apply (homEquiv _ _).injective
    ext W x
    exact (ConcreteCategory.congr_hom
      ((hom f).naturality (BaseChangeComparison.overIso g h k w W.unop).hom.op) x).symm)

/-- Scheme-relative properties respecting isomorphisms are invariant under the
comparison between iterated and direct base change. -/
theorem relative_baseChangeMap_comp_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (w : h ≫ g = k) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (MorphismProperty.inverseImage P (Over.forget U)).relative (schemeYoneda U)
        (hom (baseChangeMap h (baseChangeMap g f))) ↔
      (MorphismProperty.inverseImage P (Over.forget U)).relative (schemeYoneda U)
        (hom (baseChangeMap k f)) := by
  let eX := (forgetToPresheaf U).mapIso ((baseChangeCompNatIso g h k w).app X)
  let eY := (forgetToPresheaf U).mapIso ((baseChangeCompNatIso g h k w).app Y)
  apply MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk eX eY ?_)
  exact (forgetToPresheaf U).congr_map ((baseChangeCompNatIso g h k w).hom.naturality f).symm

/-- A relative property of the diagonal is invariant under iterated base change. -/
theorem relative_diagonal_baseChangeMap_comp_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (w : h ≫ g = k) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (MorphismProperty.inverseImage P (Over.forget U)).relative (schemeYoneda U)
        (pullback.diagonal (hom (baseChangeMap h (baseChangeMap g f)))) ↔
      (MorphismProperty.inverseImage P (Over.forget U)).relative (schemeYoneda U)
        (pullback.diagonal (hom (baseChangeMap k f))) := by
  let eX := (forgetToPresheaf U).mapIso ((baseChangeCompNatIso g h k w).app X)
  let eY := (forgetToPresheaf U).mapIso ((baseChangeCompNatIso g h k w).app Y)
  apply MorphismProperty.arrow_mk_iso_iff
    ((MorphismProperty.inverseImage P (Over.forget U)).relative
      (schemeYoneda U)).diagonal (Arrow.isoMk eX eY ?_)
  exact (forgetToPresheaf U).congr_map ((baseChangeCompNatIso g h k w).hom.naturality f).symm

variable {g h k}

/-- A chart square for a locally finite type morphism transports through isomorphisms
of both spaces. -/
theorem IsLocallyOfFiniteTypeMorphism.of_arrow_iso
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsLocallyOfFiniteTypeMorphism f) : IsLocallyOfFiniteTypeMorphism f' := by
  obtain ⟨A, B, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  refine ⟨A, B, a ≫ hom eX.hom, b ≫ hom eY.hom, φ,
    ha.comp_iso ((forgetToPresheaf S).mapIso eX),
    hs.comp_iso ((forgetToPresheaf S).mapIso eX),
    hb.comp_iso ((forgetToPresheaf S).mapIso eY), hφ, ?_⟩
  have ww := (forgetToPresheaf S).congr_map w
  change hom eX.hom ≫ hom f' = hom f ≫ hom eY.hom at ww
  rw [Category.assoc, ww, ← Category.assoc, hw, Category.assoc]

/-- Smoothness transports through an isomorphism of arrows of algebraic spaces. -/
theorem IsSmoothMorphism.of_arrow_iso
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsSmoothMorphism f) : IsSmoothMorphism f' := by
  obtain ⟨A, B, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  refine ⟨A, B, a ≫ hom eX.hom, b ≫ hom eY.hom, φ,
    ha.comp_iso ((forgetToPresheaf S).mapIso eX),
    hs.comp_iso ((forgetToPresheaf S).mapIso eX),
    hb.comp_iso ((forgetToPresheaf S).mapIso eY), hφ, ?_⟩
  have ww := (forgetToPresheaf S).congr_map w
  change hom eX.hom ≫ hom f' = hom f ≫ hom eY.hom at ww
  rw [Category.assoc, ww, ← Category.assoc, hw, Category.assoc]

section StageToLimit

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (r : j ⟶ i) {X Y : AlgebraicSpace (D.obj i)} (f : X ⟶ Y)

/-- A representable scheme-relative property holding at a later stage holds over
any cone point. No finiteness or limit hypothesis is needed in this direction. -/
theorem relative_baseChangeMap_of_stage (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hf : (MorphismProperty.inverseImage P (Over.forget (D.obj j))).relative
      (schemeYoneda (D.obj j)) (hom (baseChangeMap (D.map r) f))) :
    (MorphismProperty.inverseImage P (Over.forget c.pt)).relative (schemeYoneda c.pt)
      (hom (baseChangeMap (c.π.app i) f)) := by
  apply (relative_baseChangeMap_comp_iff (D.map r) (c.π.app j) (c.π.app i)
    P (c.w r) f).mp
  exact relative_restrictPresheaf_map P hf

/-- Separatedness at a later stage implies separatedness over any cone point. -/
theorem isSeparatedMorphism_baseChangeMap_of_stage
    (hf : IsSeparatedMorphism (baseChangeMap (D.map r) f)) :
    IsSeparatedMorphism (baseChangeMap (c.π.app i) f) := by
  apply (relative_diagonal_baseChangeMap_comp_iff (D.map r) (c.π.app j) (c.π.app i)
    @_root_.AlgebraicGeometry.IsClosedImmersion (c.w r) f).mp
  exact hf.baseChangeMap

/-- Smoothness at a later stage implies smoothness over any cone point. -/
theorem isSmoothMorphism_baseChangeMap_of_stage
    (hf : IsSmoothMorphism (baseChangeMap (D.map r) f)) :
    IsSmoothMorphism (baseChangeMap (c.π.app i) f) := by
  let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
  exact IsSmoothMorphism.of_arrow_iso (e.app X) (e.app Y) (e.hom.naturality f).symm
    hf.baseChangeMap

end StageToLimit

end Langlands.AlgebraicGeometry.AlgebraicSpace
