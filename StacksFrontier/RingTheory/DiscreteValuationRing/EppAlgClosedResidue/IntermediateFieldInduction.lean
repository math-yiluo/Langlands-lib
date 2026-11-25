module

public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.SolvableInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TameCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.FiniteLevelCyclotomic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: induction over intermediate fields

The prime-degree step, inertia fixed fields, the induction over intermediate fields, and Epp's
theorem in the complete case (Tag 09F8).

Part of `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue`;
see there for the overview and references.
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

open scoped TensorProduct

universe uK₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerABB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKK₁L₁

universe uF uD₁ uD₂ uD₃

universe u v

universe uL₁ uA₁ uB₁

/-- The integral closure in the fixed field of the inertia group is formally unramified.

When the fixed field is everything, no extension is needed at all, and this with
`isWeaklyUnramified_of_formallyUnramified` is why. -/
theorem formallyUnramified_integralClosure_fixedField_inertia
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    [IsLocalRing (integralClosure A L)] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    let E := IntermediateField.fixedField
      ((IsLocalRing.maximalIdeal (integralClosure A L)).inertia Gal(L/K))
    IsLocalRing (integralClosure A E) → Algebra.FormallyUnramified A (integralClosure A E)
 := by
  classical
  let R := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L R
  let : SMulCommClass Gal(L/K) A R :=
    ⟨fun g a b => by
      simp only [Algebra.smul_def]
      change galRestrict A K L R g (algebraMap A R a * b) =
        algebraMap A R a * galRestrict A K L R g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let P := IsLocalRing.maximalIdeal R
  let I := P.inertia Gal(L/K)
  let E := IntermediateField.fixedField I
  let S := integralClosure A E
  dsimp only
  intro hS
  let : IsLocalRing S := hS
  let R' := FixedPoints.subalgebra A R I
  let inclusion : R' →ₐ[A] L := R.val.comp R'.val
  let iota : R' →ₐ[A] E :=
    inclusion.codRestrict (E.toSubalgebra.restrictScalars A) (fun b => by
      change (inclusion b : L) ∈ E
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (algebraMap_galRestrict_apply A g (b : R)).symm.trans
        (congrArg (algebraMap R L) (b.property ⟨g, hg⟩)))
  let : Algebra R' E := iota.toAlgebra
  let : IsScalarTower A R' E := IsScalarTower.of_algebraMap_eq fun a => (iota.commutes a).symm
  obtain ⟨hIC, het⟩ :=
    IsDiscreteValuationRing.inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization A K L P
  let : IsIntegralClosure R' A E := hIC
  let e : S ≃ₐ[A] R' := IsIntegralClosure.equiv A S E R'
  let : IsLocalRing R' := e.toRingEquiv.isLocalRing
  let : Algebra.IsIntegral R' R := Algebra.IsIntegral.tower_top A
  let : IsLocalHom (algebraMap R' R) := Algebra.IsIntegral.isLocalHom R' R
  let q := P.under R'
  have hq : q = IsLocalRing.maximalIdeal R' := IsLocalRing.maximalIdeal_comap (algebraMap R' R)
  let : Algebra.Etale A (Localization.AtPrime q) := het
  let l : R' ≃ₐ[R'] Localization.AtPrime q := IsLocalization.atUnits R' q.primeCompl (by
    intro x hx
    change IsUnit x
    simpa only [hq, Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] using hx)
  let e' : S ≃ₐ[A] Localization.AtPrime q := e.trans (l.restrictScalars A)
  exact Algebra.FormallyUnramified.of_equiv (R := A) (A := Localization.AtPrime q) (B := S) e'.symm

/-- The inertia group of the maximal ideal is normal, so its fixed field is a normal subextension.

The fixed field is where the inertia branch of a layer recursion splits, and normality is what
lets the recursion re-enter on it. -/
theorem normal_inertia_maximalIdeal
    (G R : Type*) [Group G] [CommRing R] [IsLocalRing R] [MulSemiringAction G R] :
    ((IsLocalRing.maximalIdeal R).inertia G).Normal := by
  refine ⟨fun σ hσ τ => ?_⟩
  rw [Ideal.mem_inertia] at hσ ⊢
  intro x
  have h := hσ (τ⁻¹ • x)
  have h' : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
    exact fun hu => h ((MulEquiv.isUnit_map (MulSemiringAction.toRingAut G R τ)).mp hu)
  simpa only [mul_smul, smul_sub, smul_inv_smul] using h'

set_option backward.isDefEq.respectTransparency false in
/-- After a finite extension of a characteristic-zero field, its integral
closure contains a cyclotomic ring.

Pure field theory over a characteristic-zero base: no discrete valuation rings, no residue
fields. -/
theorem exists_finite_extension_nonempty_cyclotomicRingHom
    (A : Type*) (K : Type u) [CommRing A] [Field K] [CharZero K] [Algebra A K]
    (n : ℕ) [NeZero n] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E),
      Nonempty (CyclotomicRing n ℤ ℚ →+* integralClosure A E) := by
  let E := CyclotomicField n K
  let : Module.Finite K E := Polynomial.IsSplittingField.instFiniteDimensionalSplittingField _
  let : Polynomial.IsSplittingField ℚ (CyclotomicField n ℚ) (Polynomial.cyclotomic n ℚ) := by
    unfold CyclotomicField
    infer_instance
  let f₀ : CyclotomicField n ℚ →ₐ[ℚ] E :=
    Polynomial.IsSplittingField.lift (CyclotomicField n ℚ) (Polynomial.cyclotomic n ℚ) (by
      rw [Polynomial.map_cyclotomic]
      simpa only [Polynomial.map_cyclotomic] using
        (IsCyclotomicExtension.splits_cyclotomic K E (Set.mem_singleton n)))
  let f : CyclotomicRing n ℤ ℚ →+* E :=
    f₀.toRingHom.comp (algebraMap (CyclotomicRing n ℤ ℚ) (CyclotomicField n ℚ))
  let : Module.Finite ℤ (CyclotomicRing n ℤ ℚ) :=
    IsCyclotomicExtension.finite_of_singleton n ℤ (CyclotomicRing n ℤ ℚ)
  let g : CyclotomicRing n ℤ ℚ →+* integralClosure A E :=
    f.codRestrict (integralClosure A E).toSubring fun x =>
      ((IsIntegral.of_finite ℤ x).map f.toIntAlgHom).tower_top
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨g⟩⟩

attribute [local instance] ULift.algebra'

end IsDiscreteValuationRing
