/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
/-! Finite coefficient reduction and the canonical inverse-image square.
Source: Stacks Project, Tags 0D6D and 0E48.
(blueprint: lem-weil-pbc-finite-reduction-pullback-square) -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor proEtaleRingModulePullback
  proEtaleRingModuleAdjunction proEtaleRingDerivedAdjunction
  proEtaleAmbientRingedPullbackComparison
section Generic

private def ordinaryRestrictionIso {U V : Scheme.{t}} (u : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj SV ≅ SU)
    (h : cR.hom ≫ aU = (proEtaleSheafInverseImage u CommRingCat.{t + 1}).map aV ≫ cS.hom) :
    proEtaleRingRestrictScalars aV ⋙ proEtaleRingModulePullback u RV RU cR ≅
      proEtaleRingModulePullback u SV SU cS ⋙ proEtaleRingRestrictScalars aU :=
  @asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv u RV SV RU SU aV aU cR cS h)
    (proEtaleRingRestrictionPullbackInv_isIso u RV SV RU SU aV aU cR cS h)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
variable (r s : StrictTowerRingedSquare sq)
  (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
  (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
  (hf : r.cf.hom ≫ aX =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
  (hg : r.cg.hom ≫ aY' =
    (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
  (hg' : r.cg'.hom ≫ aX' =
    (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
  (hf' : r.cf'.hom ≫ aX' =
    (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom)

end Generic

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
