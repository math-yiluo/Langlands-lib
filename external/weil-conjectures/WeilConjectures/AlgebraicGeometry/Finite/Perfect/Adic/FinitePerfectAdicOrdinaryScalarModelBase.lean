/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison

/-! # Ordinary scalar comparison definitions and exactness -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] completedAdicChangeData completedAdicRing

/-- Ordinary completed realization, written without the later tensor-cone modules.
Source: Stacks Tags 093J and 093M. -/
abbrev finitePerfectAdicScalarModelOrdinary (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{t} A ⥤ CompletedAdicModules X d :=
  finitePerfectAdicConstant X A ⋙ completedAdicScalarExtension X d

instance finitePerfectAdicScalarModelOrdinary_additive
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    (finitePerfectAdicScalarModelOrdinary X d).Additive := by
  have := (finitePerfectAdicConstant_exact X A).1
  unfold finitePerfectAdicScalarModelOrdinary
  infer_instance

/-- Exactness of completed scalar extension, directly from completed constant flatness.
Source: Stacks Tags 093J and 093M. -/
theorem finitePerfectAdicScalarModelExtension_exact
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (completedAdicScalarExtension X d) ∧
      PreservesFiniteColimits (completedAdicScalarExtension X d) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let B := ULift.{t + 1} A
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : B)))
  let : IsNoetherianRing A := d.noetherian
  let : IsNoetherianRing B := isNoetherianRing_of_surjective A B
    (ULift.ringEquiv : B ≃+* A).symm.toRingHom (ULift.ringEquiv.symm.surjective)
  exact (exactFunctor_iff _).1
    (completed_constant_algebra_flat_quotients X I (completedAdicCommRing X d)
      (completionRingIso X d r a ha) (completedAdicScalar X d)
      (completionRingIso_scalar X d r a ha)).2.1

/-- The ordinary coefficient-universe transport. Source: Stacks Tag 05RU. -/
abbrev finitePerfectAdicScalarModelLift (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

/-- The ordinary realization of a constant quotient module on the specified slice.
Source: Stacks Tags 093J and 03CY. -/
def finitePerfectAdicOrdinaryScalarSource
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :=
  finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1)) ⋙
    constantSheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⋙
    ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left ⋙
    ProEtale.upperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom ⋙
    finitePerfectAdicScalarModules X d V U W f n

/-- Ordinary completed extension of the underlying A-module, restricted to the slice.
Source: Stacks Tags 093M and 03DJ. -/
def finitePerfectAdicOrdinaryScalarTarget
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (W : X.ProEt) (n : ℕ) :=
  ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ⋙
    finitePerfectAdicScalarModelOrdinary X d ⋙ SheafOfModules.overFunctor (completedAdicRing X d) W

/-- Exactness of the ordinary scalar source. Source: Stacks Tags 093J and 06YY. -/
theorem finitePerfectAdicOrdinaryScalarSource_exact
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    (finitePerfectAdicOrdinaryScalarSource X d V U W f n).Additive ∧
      PreservesFiniteLimits (finitePerfectAdicOrdinaryScalarSource X d V U W f n) ∧
      PreservesFiniteColimits (finitePerfectAdicOrdinaryScalarSource X d V U W f n) := by
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  unfold finitePerfectAdicOrdinaryScalarSource
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Exactness of ordinary completed realization on a slice.
Source: Stacks Tags 093M and 03DJ. -/
theorem finitePerfectAdicOrdinaryScalarTarget_exact
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (W : X.ProEt) (n : ℕ) :
    (finitePerfectAdicOrdinaryScalarTarget X d W n).Additive ∧
      PreservesFiniteLimits (finitePerfectAdicOrdinaryScalarTarget X d W n) ∧
      PreservesFiniteColimits (finitePerfectAdicOrdinaryScalarTarget X d W n) := by
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  have := (finitePerfectAdicScalarModelExtension_exact X d).1
  have := (finitePerfectAdicScalarModelExtension_exact X d).2
  have := (ringedOverFunctor_exactGeneral.{_, _, _, t + 1} (completedAdicRing X d) W).1
  have := (ringedOverFunctor_exactGeneral.{_, _, _, t + 1} (completedAdicRing X d) W).2.1
  have := (ringedOverFunctor_exactGeneral.{_, _, _, t + 1} (completedAdicRing X d) W).2.2
  unfold finitePerfectAdicOrdinaryScalarTarget finitePerfectAdicScalarModelOrdinary
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Universe transport commutes with scalar restriction, on the identical lifted action.
Source: Stacks Tag 05RU. -/
def finitePerfectAdicScalarModelLiftRestrict {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) :
    ModuleCat.restrictScalars q ⋙ finitePerfectAdicScalarModelLift B ≅
      finitePerfectAdicScalarModelLift D ⋙ ModuleCat.restrictScalars (RingHom.ulift q) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Consecutive quotient restriction commutes with coefficient-universe transport.
Source: Stacks Tag 05RU; each component is the identity linear map. -/
def finitePerfectAdicScalarModelLiftStep {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  finitePerfectAdicScalarModelLiftRestrict (Ideal.Quotient.factorPowSucc d.ideal (n + 1))

/-- Paste a coefficient square with a comparison for the remaining composite.
Source: Stacks Tag 06YY; composition and whiskering of natural isomorphisms. -/
def finitePerfectAdicPasteCoefficientStep
    {C D E E' F : Type*} [Category C] [Category D] [Category E] [Category E'] [Category F]
    {R : C ⥤ D} {L : C ⥤ E'} {H : D ⥤ E} {S : E' ⥤ E}
    {P : E ⥤ F} {Q : E' ⥤ F} (e : R ⋙ H ≅ L ⋙ S) (z : S ⋙ P ≅ Q) :
    R ⋙ H ⋙ P ≅ L ⋙ Q :=
  isoWhiskerRight e P ≪≫ isoWhiskerLeft L z

/-- The ordinary source compositor, fixed by the constant and inverse-image units.
Source: Stacks Tags 03DA, 03CY and 06YY. -/
def finitePerfectAdicOrdinaryScalarSourceStep
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ⋙
        finitePerfectAdicOrdinaryScalarSource X d V U W f (n + 1) ≅
      finitePerfectAdicOrdinaryScalarSource X d V U W f n := by
  letI : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
  let D := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let q : B →+* D := RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let UB := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
  let UD := ProEtale.upperStar (ModuleCat.{t + 1} D) U.hom
  let eC := constantCommuteCompose V.left.smallEtaleTopology
    (ModuleCat.restrictScalars.{t + 1} q)
  let eP := normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
    (ProEt.topology V.left) q
  let eU : sheafCompose (ProEt.topology V.left) (ModuleCat.restrictScalars.{t + 1} q) ⋙ UB ≅
      UD ⋙ sheafCompose (ProEt.topology U.left) (ModuleCat.restrictScalars.{t + 1} q) :=
    normalizationPullbackIso (ProEt.topology V.left)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q
  exact finitePerfectAdicPasteCoefficientStep (finitePerfectAdicScalarModelLiftStep d n)
    (finitePerfectAdicPasteCoefficientStep eC.symm
      (finitePerfectAdicPasteCoefficientStep eP
        (finitePerfectAdicPasteCoefficientStep eU
          (finitePerfectAdicScalarModulesCoherence X d V U W f n))))

/-- The ordinary target compositor is associativity of restriction along quotient maps.
Source: Stacks Tag 06YY. -/
def finitePerfectAdicOrdinaryScalarTargetStep
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (W : X.ProEt) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ⋙
        finitePerfectAdicOrdinaryScalarTarget X d W (n + 1) ≅
      finitePerfectAdicOrdinaryScalarTarget X d W n :=
  isoWhiskerRight (ModuleCat.restrictScalarsComp'
    (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm).symm
    (finitePerfectAdicScalarModelOrdinary X d ⋙
      SheafOfModules.overFunctor (completedAdicRing X d) W)

end AlgebraicGeometry.Scheme
