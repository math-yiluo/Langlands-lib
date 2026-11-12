import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.PointTopology.QuasiProjectiveWeilRestriction
import Langlands.Global.AdelicSpaceLevelPointsStatement

/-! # Comparing actual scheme and sheaf Weil restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open PointTopology

section General

variable {S S' : Scheme.{u}} (g : S' ⟶ S)
  (U : Over S') (W : Over S)

/-- Natural representing equivalences on all scheme tests identify the actual represented
presheaf with the presheaf of the fppf-sheaf Weil restriction. -/
def weilRestrictionPresheafIsoOfEquiv
    (e : ∀ T : Over S, (T ⟶ W) ≃ ((Over.pullback g).obj T ⟶ U))
    (he : ∀ {T V : Over S} (f : T ⟶ V) (p : V ⟶ W),
      e T (f ≫ p) = (Over.pullback g).map f ≫ e V p) :
    (schemeYoneda S).obj W ≅ ((weilRestriction g).obj ((schemeSheaf S').obj U)).obj :=
  NatIso.ofComponents
    (fun T => (Equiv.ulift.trans ((e T.unop).trans Equiv.ulift.symm)).toIso)
    (by
      intro T V f
      ext p
      exact congrArg ULift.up (he f.unop p.down))

/-- Any such whole-presheaf representation makes the restricted sheaf an algebraic space. -/
theorem weilRestriction_isAlgebraicSpace_of_equiv
    (e : ∀ T : Over S, (T ⟶ W) ≃ ((Over.pullback g).obj T ⟶ U))
    (he : ∀ {T V : Over S} (f : T ⟶ V) (p : V ⟶ W),
      e T (f ≫ p) = (Over.pullback g).map f ≫ e V p) :
    IsAlgebraicSpace S ((weilRestriction g).obj ((schemeSheaf S').obj U)) :=
  isAlgebraicSpace_of_presheafIso (weilRestrictionPresheafIsoOfEquiv g U W e he)
    (scheme_isAlgebraicSpace W)

end General

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
  [Module.Finite R R'] [Module.Projective R R']

section Affine

variable (U : Over (Spec (CommRingCat.of R'))) [IsAffine U.left]
  [LocallyOfFiniteType U.hom]

/-- The existing actual affine Weil scheme represents the full fppf-sheaf Weil restriction,
on arbitrary scheme tests over `Spec R`. -/
def affineWeilRestrictionPresheafIso :
    (schemeYoneda _).obj (affineWeilRestriction R R' U) ≅
      ((ringWeilRestriction R R').obj ((schemeSheaf _).obj U)).obj :=
  weilRestrictionPresheafIsoOfEquiv (Spec.algebraMap R R') U
    (affineWeilRestriction R R' U) (affineWeilRestrictionTestEquiv R R' U)
    (affineWeilRestrictionComparison_natural R R' U)

/-- The forward component is the actual base-change and counit comparison. -/
@[simp]
theorem affineWeilRestrictionPresheafIso_hom_app
    (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ affineWeilRestriction R R' U) :
    (affineWeilRestrictionPresheafIso R R' U).hom.app (op T) (ULift.up p) =
      ULift.up (affineWeilRestrictionComparison R R' U T p) :=
  rfl

/-- Restriction of an affine finite-type scheme is an algebraic space, represented by the
previously constructed affine scheme. -/
theorem affineWeilRestriction_isAlgebraicSpace :
    IsAlgebraicSpace _ ((ringWeilRestriction R R').obj ((schemeSheaf _).obj U)) :=
  isAlgebraicSpace_of_presheafIso (affineWeilRestrictionPresheafIso R R' U)
    (scheme_isAlgebraicSpace (affineWeilRestriction R R' U))

/-- The affine scheme representation gives a finite-type atlas for the actual restricted
sheaf, for every proof of its algebraic-space property. -/
theorem affineWeilRestriction_finiteType
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj ((schemeSheaf _).obj U))) :
    FiniteTypeOverRing R (ringWeilRestrictionSpace R R' ((schemeToSpace _).obj U) h) :=
  (HasAtlasProperty.of_scheme (affineWeilRestriction R R' U)
    ⟨inferInstance, affineWeilRestriction_quasiCompact R R' U⟩).of_iso
      (affineWeilRestrictionPresheafIso R R' U)

end Affine

section FiniteAffineNeighborhoods

variable (Y : Over (Spec (CommRingCat.of R'))) [LocallyOfFiniteType Y.hom]
  [_root_.AlgebraicGeometry.IsSeparated Y.hom] (hY : HasFiniteAffineNeighborhoods Y.left)

/-- The glued actual Weil scheme represents the sheaf restriction when finite sets have
affine neighborhoods. -/
def affineChartWeilRestrictionPresheafIso :
    (schemeYoneda _).obj (affineChartWeilRestriction R R' Y) ≅
      ((ringWeilRestriction R R').obj ((schemeSheaf _).obj Y)).obj :=
  weilRestrictionPresheafIsoOfEquiv (Spec.algebraMap R R') Y
    (affineChartWeilRestriction R R' Y) (affineChartWeilRestrictionTestEquiv R R' Y hY)
    (affineChartWeilRestrictionTestEquiv_natural R R' Y hY)

@[simp]
theorem affineChartWeilRestrictionPresheafIso_hom_app
    (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ affineChartWeilRestriction R R' Y) :
    (affineChartWeilRestrictionPresheafIso R R' Y hY).hom.app (op T) (ULift.up p) =
      ULift.up (affineChartWeilRestrictionComparison R R' Y T p) :=
  rfl

end FiniteAffineNeighborhoods

section ProjectiveImmersion

variable (Y : Over (Spec (CommRingCat.of R'))) [LocallyOfFiniteType Y.hom]

/-- An actual projective immersion supplies a representation of the fppf-sheaf Weil
restriction by the existing glued scheme. -/
def projectiveImmersionWeilRestrictionPresheafIso
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace R' n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec R' n = Y.hom) :
    (schemeYoneda _).obj (affineChartWeilRestriction R R' Y) ≅
      ((ringWeilRestriction R R').obj ((schemeSheaf _).obj Y)).obj :=
  weilRestrictionPresheafIsoOfEquiv (Spec.algebraMap R R') Y
    (affineChartWeilRestriction R R' Y)
    (projectiveImmersionWeilRestrictionTestEquiv R R' Y n i hi)
    (projectiveImmersionWeilRestrictionTestEquiv_natural R R' Y n i hi)

@[simp]
theorem projectiveImmersionWeilRestrictionPresheafIso_hom_app
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace R' n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec R' n = Y.hom)
    (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ affineChartWeilRestriction R R' Y) :
    (projectiveImmersionWeilRestrictionPresheafIso R R' Y n i hi).hom.app (op T)
      (ULift.up p) = ULift.up (affineChartWeilRestrictionComparison R R' Y T p) :=
  rfl

end ProjectiveImmersion

end Langlands.AlgebraicGeometry.AlgebraicSpace
