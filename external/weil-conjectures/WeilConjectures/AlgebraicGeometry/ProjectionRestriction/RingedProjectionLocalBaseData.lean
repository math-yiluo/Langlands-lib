/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceTotalTensorComparison
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ExactTensor.ProjectionExactTensorComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionLocalOrdinaryResolving
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! Base restriction and tensor data for localized projection sites.

## References

* Stacks Project, Modules on Sites, Tag 04J0
* Cohomology on Sites, Tags 08FI, 0FN5 and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option linter.privateModule false

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- The restriction and tensor portion of localized projection data.

This package records the localized module operation, its derived adjunction,
and all normalized tensor models and comparisons.  The direct-image and
pullback comparison maps are supplied separately by the derived package. -/
structure LocalBaseData {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    (g : Global f R_Y R_X c) (V : Y.ProEt) where
  [restrictionYAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).Additive]
  [restrictionXAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)).Additive]
  restrictionY : Restriction R_Y V
  restrictionX : Restriction R_X ((proEtaleBaseChange f).obj V)
  operation : Operation (Over.post (X := V) (proEtaleBaseChange f)) (R_Y.over V)
    (R_X.over ((proEtaleBaseChange f).obj V))
  coefficient_sections : ∀ T : Over V, operation.coefficient.hom.app (op T) =
    g.operation.coefficient.hom.app (op T.left)
  adjunction : operation.DerivedAdjunction
  tensorY : TensorModel (R_Y.over V)
  tensorX : TensorModel (R_X.over ((proEtaleBaseChange f).obj V))
  tensorYShifts : TensorShifts tensorY
  tensorXShifts : TensorShifts tensorX
  ordinaryTensor : operation.OrdinaryTensor
  tensorComparison : TensorComparison operation.pullback operation.leftModel tensorY tensorX
    ordinaryTensor.iso
  tensorComparison_shifts : TensorComparisonShifts tensorComparison
    (sa := tensorYShifts) (sb := tensorXShifts) (sd := inferInstance)
  restrictionTensorY : TensorComparison
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V)
    restrictionY.model g.tensorY tensorY restrictionY.ordinaryTensor
  restrictionTensorX : TensorComparison
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V))
    restrictionX.model g.tensorX tensorX restrictionX.ordinaryTensor
  restrictionTensorY_shifts :
    TensorComparisonShifts restrictionTensorY
      (sa := g.tensorYShifts) (sb := tensorYShifts) (sd := inferInstance)
  restrictionTensorX_shifts :
    TensorComparisonShifts restrictionTensorX
      (sa := g.tensorXShifts) (sb := tensorXShifts) (sd := inferInstance)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem restrictionWithTensor_exists {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) (V : C)
    (a : TensorModel R) (sa : TensorShifts a) :
    ∃ (r : Restriction R V) (b : TensorModel (R.over V)) (sb : TensorShifts b),
      let L : Mod R ⥤ Mod (R.over V) := SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V
      letI : L.Additive := r.additive
      ∃ t : TensorComparison L r.model a b r.ordinaryTensor,
        TensorComparisonShifts t (sa := sa) (sb := sb) (sd := inferInstance) := by
  obtain ⟨_, _, _, ha, hl, hc⟩ :=
    SheafOfModules.localizedSystemExact.{u + 1, u, 0} R V
  let r : Restriction R V := {
    additive := ha
    limits := hl
    colimits := hc
    ordinaryTensor := CategoryTheory.tensorOverIso.{u + 1, u, 0} J R V
    pure_sections := fun M N W x y ↦
      CategoryTheory.tensorOverIso_pure.{u + 1, u, 0} J R V M N W.unop x y }
  let L : Mod R ⥤ Mod (R.over V) := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V
  have : L.Additive := ha
  have : PreservesFiniteLimits L := hl
  have : PreservesFiniteColimits L := hc
  have : PreservesColimitsOfSize.{u + 1, u + 1} L :=
    CategoryTheory.slice_pushforward_colimits (𝟙 _)
  have : PreservesColimitsOfSize.{0, 0} L := preservesSmallestColimits_of_preservesColimits L
  obtain ⟨b, ⟨sb⟩⟩ := tensorModelWithShifts_nonempty (R.over V)
  have hn : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
        (r.ordinaryTensor M' N').hom =
      (r.ordinaryTensor M N).hom ≫ (((tensor (R.over V)).map (L.map f)).app (L.obj N) ≫
        ((tensor (R.over V)).obj (L.obj M')).map (L.map g)) := by
    intro M M' N N' f g
    exact CategoryTheory.tensorOverIso_naturality.{u + 1, u, 0} J R V f g
  have hp : ∀ P, resolving R P → resolving (R.over V)
      ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
    intro P hP
    refine ⟨(SheafOfModules.ringedSite_restriction_exact_kflat.{u + 1, u, 0}
      J R V).2.2 P hP.1, ?_⟩
    intro n
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, 0}
      (R.over V) ((P.X n).over V)).2
    intro W m coeff sections hrel
    obtain ⟨Z, hZ, h⟩ :=
      (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, 0}
        R (P.X n)).1
        (hP.2 n) W.left m coeff sections hrel
    refine ⟨(Sieve.overEquiv W).symm Z, ?_, ?_⟩
    · exact (J.mem_over_iff _).2 (by simpa using hZ)
    · intro T f hf
      exact h T.left f.left hf
  obtain ⟨t, ht⟩ := ExactTensor.exactTensorComparison_exists
    L a b sa sb r.ordinaryTensor hn hp
  exact ⟨r, b, sb, t, ht⟩

/-- For every object `V` of the pro-etale site of `Y`, the base restriction and tensor data
`LocalBaseData g V` (localized coefficient restriction, its derived adjunction and the tensor
comparisons) exists. -/
theorem localBaseData_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) :
    Nonempty (LocalBaseData g V) := by
  obtain ⟨rY, a, sa, tY, htY⟩ :=
    restrictionWithTensor_exists R_Y V g.tensorY g.tensorYShifts
  obtain ⟨rX, b, sb, tX, htX⟩ := restrictionWithTensor_exists
    R_X ((proEtaleBaseChange f).obj V) g.tensorX g.tensorXShifts
  obtain ⟨o, hcoeff, mu, hp⟩ := localOrdinaryResolving_exists f R_Y R_X c g V
  let := o.moduleAdjunction.isLeftAdjoint
  obtain ⟨t, ht⟩ := ExactTensor.exactTensorComparison_exists
    o.pullback a b sa sb mu.iso (ordinary_naturality o mu) hp
  exact ⟨{
    restrictionYAdditive := rY.additive
    restrictionXAdditive := rX.additive
    restrictionY := rY
    restrictionX := rX
    operation := o
    coefficient_sections := hcoeff
    adjunction := operationDerivedAdjunction o
    tensorY := a
    tensorX := b
    tensorYShifts := sa
    tensorXShifts := sb
    ordinaryTensor := mu
    tensorComparison := t
    tensorComparison_shifts := ht
    restrictionTensorY := tY
    restrictionTensorX := tX
    restrictionTensorY_shifts := htY
    restrictionTensorX_shifts := htX }⟩

end AlgebraicGeometry.Scheme.ProjectionRestriction
