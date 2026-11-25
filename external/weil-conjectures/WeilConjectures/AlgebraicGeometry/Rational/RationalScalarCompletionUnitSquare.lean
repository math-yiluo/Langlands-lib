/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.CategoryTheory.ReflectedCoefficient.Arrow.ReflectedAdjunctionCoefficientSquares
public import WeilConjectures.CategoryTheory.Ringed.RingedPushforwardCompletion
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Finite scalar change and completed pullback with the actual units

The coefficient maps, derived tensors, raw categories and quotient-tower units are
those of the imported dependency nodes. Comparison arrows below only orient the
canonical comparisons and transport them through the unit-normalized
ambient quotient comparison.

## References

* Stacks 099M and 099N (2), (5)
* Stacks 099M, 099N, 0A0E and 0A0G
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def scalarUnitIso {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.unit (reductionModuleRing W R) ≅
      (pbcRestrict e.hom).obj (SheafOfModules.unit (reductionModuleRing W S)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      let eU := Iso.commRingCatIsoToRingEquiv
        (((sheafToPresheaf (ProEt.topology W) CommRingCat).mapIso e).app U)
      ModuleCat.isoMk eU.toAddEquiv.toAddCommGrpIso
        (by intro r; ext x; exact ((e.hom.hom.app U).hom.map_mul r x).symm))
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) x))

/-- The quotient-tower construction is ordinary pullback followed by reflection,
including the actual augmentation, on arbitrary ambient complexes. -/
theorem pbcActualAmbientCompletedPullback_tower
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! e : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d,
      ∀ K : PbcCompletedDerived Y d,
        (pbcActualStrictCompletedPullUnit d g).app K ≫ e.hom.app K =
          (pbcActualCompletedPullUnit g d).app K := by
  classical
  let L := pbcActualDerivedPull g d
  let R := completedTowerRlim d X
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let t : completedReductionTower Y d ⋙ completedTowerPullback g d ≅
      L ⋙ completedReductionTower X d :=
    Functor.isoWhiskerLeft (completedReductionTower Y d) eT ≪≫ τ ≪≫
      Functor.isoWhiskerRight eL.symm (completedReductionTower X d)
  have ht (K : PbcCompletedDerived Y d) :
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
          t.hom.app K = (completedReductionTowerUnit d X).app (L.obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := actualCompletion_quotient d X
  let b : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
    Functor.isoWhiskerRight t R ≪≫ Functor.associator L (completedReductionTower X d) R ≪≫
      Functor.isoWhiskerLeft L c.symm
  have hb (K : PbcCompletedDerived Y d) :
      (pbcActualStrictCompletedPullUnit d g).app K ≫ b.hom.app K =
        (pbcActualCompletedPullUnit g d).app K := by
    have hu : completedPullbackComparison g d K ≫ R.map (t.hom.app K) =
        d.completionUnit X (L.obj K) := by
      dsimp only [completedPullbackComparison]
      rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
      rfl
    simp only [pbcActualStrictCompletedPullUnit, pbcActualCompletedPullUnit, b,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.comp_obj, Iso.symm_hom]
    change completedPullbackComparison g d K ≫
      (R.map (t.hom.app K) ≫ c.inv.app (L.obj K)) =
        (pbcActualCompletionUnit d X).app (L.obj K)
    rw [← Category.assoc, hu, ← hc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  refine ⟨b, hb, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  apply (cancel_epi (b.inv.app K)).1
  apply (actualReflection d X (L.obj K)
    ((pbcActualCompletedPull g d).obj K)
    (pbcActualCompletedPull_isComplete g d K)).injective
  have hi : (pbcActualCompletedPullUnit g d).app K ≫ b.inv.app K =
      (pbcActualStrictCompletedPullUnit d g).app K := by
    rw [← hb K, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  change (pbcActualCompletedPullUnit g d).app K ≫
      (b.inv.app K ≫ e'.hom.app K) =
    (pbcActualCompletedPullUnit g d).app K ≫ (b.inv.app K ≫ b.hom.app K)
  rw [← Category.assoc, ← Category.assoc, hi, he']
  exact (hb K).symm

/-- The uniquely augmentation-normalized ambient comparison; no unrelated map is chosen. -/
def pbcActualAmbientCompletedPullbackIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
  (pbcActualAmbientCompletedPullback_tower d g).exists.choose

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (i : E →ₐ[ℚ_[l]] L)

/-- The inverse reflected coefficient-square comparison, with the normalization. -/
def rationalScalarReflectedBeta {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙ pbcEmbeddingAmbientTensor l E L i X ≅
      pbcEmbeddingAmbientTensor l E L i Y ⋙ pbcActualCompletedPull g (pbcIntegralDatum l L) :=
  (pbcScalarCompletedPullIso l E L i g).symm

/-- The same comparison on the actual quotient-tower functors, retaining both units. -/
def rationalScalarStrictBeta {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙
        pbcEmbeddingAmbientTensor l E L i X ≅
      pbcEmbeddingAmbientTensor l E L i Y ⋙
        pbcActualStrictCompletedPull (pbcIntegralDatum l L) g :=
  Functor.isoWhiskerRight (pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l E) g)
      (pbcEmbeddingAmbientTensor l E L i X) ≪≫
    rationalScalarReflectedBeta l E L i g ≪≫
      Functor.isoWhiskerLeft (pbcEmbeddingAmbientTensor l E L i Y)
        (pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l L) g).symm

variable {X Y : Scheme.{u}}

end AlgebraicGeometry.Scheme
