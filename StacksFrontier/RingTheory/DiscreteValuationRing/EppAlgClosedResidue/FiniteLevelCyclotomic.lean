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
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TotallyRamifiedTensor

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: finite levels and the cyclotomic Galois case

The finite-level induction, the Galois case over a cyclotomic field, and normal field factors.

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

/-- The cyclotomic parameter has positive finite valuation in mixed characteristic. -/
theorem exists_irreducible_associated_pow_wElt
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    (f : CyclotomicRing p ℤ ℚ →+* B) :
    ∃ (π : B) (e : ℕ), Irreducible π ∧ 0 < e ∧ Associated (wElt f) (π ^ e) := by
  have hw : wElt f ≠ 0 := by
    intro h
    have hz : zetaA f = 1 := (sub_eq_zero.mp h).symm
    have hp := zetaA_geom_sum_eq_zero f
    simp only [hz, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  have hpow : (zetaA f) ^ p = 1 := by
    dsimp [zetaA]
    rw [← map_pow]
    exact (congrArg f (IsCyclotomicExtension.zeta_spec p ℤ
      (CyclotomicRing p ℤ ℚ)).pow_eq_one).trans (map_one f)
  have hres : IsLocalRing.residue B (wElt f) = 0 := by
    have hpowRes : (IsLocalRing.residue B (zetaA f)) ^ p = 1 := by
      simpa only [map_pow, map_one] using congrArg (IsLocalRing.residue B) hpow
    have hzero : (IsLocalRing.residue B (zetaA f) - 1) ^ p = 0 := by
      rw [sub_pow_char, hpowRes, one_pow, sub_self]
    have hz : IsLocalRing.residue B (zetaA f) = 1 :=
      sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
    simp only [wElt, map_sub, map_one, hz, sub_self]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw hπ
  refine ⟨π, e, hπ, Nat.pos_of_ne_zero ?_, he⟩
  intro he0
  have hu : IsUnit (wElt f) := he.isUnit_iff.mpr (by simp [he0])
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

/-- A map out of a finite product of algebras factors through one component. -/
theorem AlgHom.exists_comp_evalAlgHom_eq
    (R T : Type*) [CommRing R] [CommRing T] [IsDomain T] [Algebra R T]
    {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] (f : (∀ i, S i) →ₐ[R] T) :
    ∃ (i : ι) (g : S i →ₐ[R] T), g.comp (Pi.evalAlgHom R S i) = f
 := by
  classical
  let q : PrimeSpectrum (∀ i, S i) := ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime _⟩
  obtain ⟨i, r, hr⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq q
  have hr' : r.asIdeal.comap (Pi.evalRingHom S i) = RingHom.ker f.toRingHom :=
    congrArg PrimeSpectrum.asIdeal hr
  have hker : RingHom.ker (Pi.evalAlgHom R S i).toRingHom ≤ RingHom.ker f.toRingHom := by
    rw [← hr']
    exact Ideal.comap_mono bot_le
  have hsurj : Function.Surjective (Pi.evalAlgHom R S i) :=
    Function.surjective_eval i
  exact ⟨i, (Pi.evalAlgHom R S i).liftOfSurjective hsurj f hker,
    (Pi.evalAlgHom R S i).liftOfSurjective_comp hsurj f hker⟩

/-- Normality and the degree bound transfer along a surjection out of a base-changed tensor
product. -/
theorem normal_and_finrank_le_of_surjective_tensorProduct
    (F E K L : Type*) [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L] [Algebra E L] [Algebra K L]
    [IsScalarTower F E L] [IsScalarTower F K L]
    [Module.Finite F E] [Normal F E]
    (hsurj : Function.Surjective
      ((AlgHom.liftEquiv F K E L) (IsScalarTower.toAlgHom F E L))) :
    Module.Finite K L ∧ Normal K L ∧ Module.finrank K L ≤ Module.finrank F E
 := by
  let φ := (AlgHom.liftEquiv F K E L) (IsScalarTower.toAlgHom F E L)
  let : Module.Finite K L := Module.Finite.of_surjective φ.toLinearMap hsurj
  have hbound : Module.finrank K L ≤ Module.finrank F E := by
    simpa only [Module.finrank_baseChange] using
      (LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj)
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap E L)) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨t, rfl⟩ := hsurj x
    induction t using TensorProduct.inductionOn with
    | tmul k e =>
      change φ (k ⊗ₜ[F] e) ∈ _
      rw [AlgHom.liftEquiv_tmul]
      exact (IntermediateField.adjoin K (Set.range (algebraMap E L))).smul_mem
        (IntermediateField.subset_adjoin K (Set.range (algebraMap E L)) ⟨e, rfl⟩)
    | add t₁ t₂ h₁ h₂ => simpa only [map_add] using (IntermediateField.adjoin K _).add_mem h₁ h₂
  refine ⟨inferInstance, normal_iff.mpr ?_, hbound⟩
  intro x
  refine ⟨IsIntegral.of_finite K x, IntermediateField.splits_of_mem_adjoin K L
    (S := Set.range (algebraMap E L)) ?_ ?_⟩
  · rintro y ⟨e, rfl⟩
    refine ⟨IsIntegral.of_finite K _, ?_⟩
    have hs := (Normal.splits' (F := F) e).map (algebraMap E L)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at hs
    have hd := Polynomial.map_dvd (algebraMap K L)
      (minpoly.dvd_map_of_isScalarTower F K (algebraMap E L e))
    have hm : minpoly F (algebraMap E L e) = minpoly F e :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom F E L)
        (IsScalarTower.toAlgHom F E L).injective e
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hm] at hd
    exact hs.of_dvd (Polynomial.map_ne_zero (minpoly.ne_zero (IsIntegral.of_finite F e))) hd
  · rw [hgen]
    trivial

/-- In a finite flat local extension of domains, the ramification index divides its rank.

At a member of a layer recursion whose upper layer has degree one this is what forces the
ramification index there to be one, with no hypothesis on the residue field at all. -/
theorem ramificationIdx_dvd_finrank_of_isLocalRing
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain R]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Module.Flat R S] :
    (IsLocalRing.maximalIdeal S).ramificationIdx R ∣ Module.finrank R S
 := by
  classical
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  let : Unique (p.primesOver S) :=
    { default := Ideal.primesOver.mk p q
      uniq P := Subtype.ext (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P.1 (by
          rw [← Ideal.over_def P.1 p]
          infer_instance))) }
  have h := Ideal.sum_ramification_inertia_eq_finrank p S
  have heq : q.ramificationIdx R * q.inertiaDeg R = Module.finrank R S := by
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    rw [show (default : p.primesOver S) = Ideal.primesOver.mk p q from Subsingleton.elim _ _] at h
    exact h
  exact ⟨q.inertiaDeg R, heq.symm⟩

/-- **At a factor of the upper base change, the matching factor of the lower one, with
normality and a degree bound.**

This is what makes the layer recursion's re-entry possible: the new members are the factors `F`
of `(M ⊗[K] N)ᵣₑd` over the factors `H i` of `(L ⊗[K] N)ᵣₑd`, and
`Stacks.EppTheorem.FamilyTowerSolvable` requires each to be `Normal` and of bounded degree.

The bound is `≤ Module.finrank L M`, not `<`. A recursion gets its strict decrease from having
already absorbed a bottom layer — apply this with `L` the bottom layer's top — not from
here. -/
theorem exists_fieldFactor_normal_and_finrank_le
    (K L M N F : Type*) [Field K] [Field L] [Field M] [Field N] [Field F]
    [Algebra K L] [Algebra L M] [Algebra K M] [Algebra K N]
    [Algebra K F] [Algebra L F] [Algebra M F] [Algebra N F]
    [IsScalarTower K L M] [IsScalarTower K M F] [IsScalarTower K L F]
    [IsScalarTower L M F] [IsScalarTower K N F]
    [Module.Finite L M] [Normal L M]
    {ι : Type*} [Finite ι] (H : ι → Type*) [∀ i, Field (H i)]
    [∀ i, Algebra L (H i)] [∀ i, Algebra N (H i)] :
    letI : Algebra N (L ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra N (M ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra N (ReducedTensorTower.Reduction (L ⊗[K] N)) := Ideal.Quotient.algebra N
    ∀ (e : ReducedTensorTower.Reduction (L ⊗[K] N) ≃ₐ[N] ∀ i, H i)
      (_ : ∀ i l, e (Ideal.Quotient.mk _ (l ⊗ₜ[K] (1 : N))) i = algebraMap L (H i) l)
      (φ : (M ⊗[K] N) →ₐ[N] F)
      (_ : ∀ m n, φ (m ⊗ₜ[K] n) = algebraMap M F m * algebraMap N F n)
      (_ : Function.Surjective φ),
      ∃ (i : ι) (g : H i →ₐ[N] F),
        letI : Algebra (H i) F := g.toRingHom.toAlgebra
        IsScalarTower L (H i) F ∧ Module.Finite (H i) F ∧ Normal (H i) F ∧
          Module.finrank (H i) F ≤ Module.finrank L M
 := by
  let : Algebra N (L ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
  let : Algebra N (M ⊗[K] N) := Algebra.TensorProduct.rightAlgebra
  let : Algebra N (ReducedTensorTower.Reduction (L ⊗[K] N)) := Ideal.Quotient.algebra N
  intro e he φ hφ hsurj
  let ι : (L ⊗[K] N) →ₐ[N] M ⊗[K] N :=
    { __ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K N)).toRingHom
      commutes' n := by
        change algebraMap L M 1 ⊗ₜ[K] n = (1 : M) ⊗ₜ[K] n
        rw [map_one] }
  have hι (l : L) (n : N) : ι (l ⊗ₜ[K] n) = algebraMap L M l ⊗ₜ[K] n := rfl
  let r : ReducedTensorTower.Reduction (L ⊗[K] N) →ₐ[N] F :=
    Ideal.Quotient.liftₐ _ (φ.comp ι) fun t ht =>
      ((mem_nilradical.mp ht).map (φ.comp ι)).eq_zero
  obtain ⟨i, g, hg⟩ := AlgHom.exists_comp_evalAlgHom_eq N F H (r.comp e.symm.toAlgHom)
  have hfactor (t : L ⊗[K] N) : g (e (Ideal.Quotient.mk _ t) i) = φ (ι t) := by
    have h := congrArg (fun f : (∀ i, H i) →ₐ[N] F => f (e (Ideal.Quotient.mk _ t))) hg
    change g (e (Ideal.Quotient.mk _ t) i) = r (e.symm (e (Ideal.Quotient.mk _ t))) at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h.trans (by
      change (Ideal.Quotient.lift _ (φ.comp ι).toRingHom _) (Ideal.Quotient.mk _ t) = _
      rw [Ideal.Quotient.lift_mk]
      rfl)
  let : Algebra (H i) F := g.toRingHom.toAlgebra
  let : IsScalarTower N (H i) F := IsScalarTower.of_algHom g
  let : IsScalarTower L (H i) F := IsScalarTower.of_algebraMap_eq fun l => by
    change algebraMap L F l = g (algebraMap L (H i) l)
    rw [← he i l, hfactor, hι, hφ, map_one, mul_one,
      ← IsScalarTower.algebraMap_apply L M F]
  let ψ := (AlgHom.liftEquiv L (H i) M F) (IsScalarTower.toAlgHom L M F)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨t, rfl⟩ := hsurj x
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
      refine ⟨algebraMap N (H i) n ⊗ₜ[L] m, ?_⟩
      rw [AlgHom.liftEquiv_tmul, Algebra.smul_def, hφ]
      change g (algebraMap N (H i) n) * algebraMap M F m = _
      rw [g.commutes, mul_comm]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨x₁, hx₁⟩ := h₁
      obtain ⟨x₂, hx₂⟩ := h₂
      exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂, map_add]⟩
  exact ⟨i, g, inferInstance, normal_and_finrank_le_of_surjective_tensorProduct L M (H i) F hψ⟩

end IsDiscreteValuationRing
