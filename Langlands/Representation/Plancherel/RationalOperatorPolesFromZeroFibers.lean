import Langlands.Representation.Plancherel.RationalRankOneOperatorDenominator
import Langlands.Representation.Plancherel.RationalUnramifiedLocalDivisibilityProof
import Langlands.Representation.Plancherel.PolynomialOperatorFactorDivision
import Langlands.Representation.Plancherel.LaurentRankOnePrimeDivisors
import Langlands.Representation.Plancherel.UnramifiedNormalizedModels
import Mathlib.Data.List.Prime
import Mathlib.Order.WellFounded

/-! # Whole-operator pole support from the zeros of cleared numerators -/

noncomputable section

set_option maxRecDepth 4096

universe u uV uW

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.RationalOperatorPolePresentation

open UnramifiedOperatorFamily LaurentBlockInvariants

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H)

local instance pointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
set_option quotPrecheck false in
local notation "ν" => fun a => (rationalNormCharacters H a).toMul
local notation "X" => unramifiedCharacters ν
local notation "U" => unitaryUnramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "hp" => continuous_rationalValuationImageProjection H

private def factorization_of_associated {a b : R}
    (A : RationalUnitaryPoleFactorization H a) (h : Associated a b) :
    RationalUnitaryPoleFactorization H b :=
  Classical.choice (by
    obtain ⟨r, hr⟩ := h
    refine ⟨⟨A.poles, A.remainder * (r : R), ?_, ?_⟩⟩
    · rw [← mul_assoc]
      exact hr.symm.trans (congrArg (fun d : R => d * (r : R)) A.factorization)
    · intro z
      let ev := UnramifiedNormalized.evaluation ν (unitaryToUnramified H z)
      exact mul_ne_zero (A.remainder_nonzero z) ((Units.isUnit r).map ev).ne_zero)

include hH in
private def ofDvdPrime {p b : R} (hprime : Prime p) (hpb : p ∣ b)
    (B : RationalUnitaryPoleFactorization H b) : RationalUnitaryPoleFactorization H p :=
  Classical.choice (by
    classical
    let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
    by_cases hnv : ∀ z : U, p.val (unitaryToUnramified H z) ≠ 0
    · exact ⟨RationalUnitaryPoleFactorization.ofNonvanishing H p hnv⟩
    push Not at hnv
    obtain ⟨z, hz⟩ := hnv
    let ev := UnramifiedNormalized.evaluation ν (unitaryToUnramified H z)
    have hnd : ¬ p ∣ B.remainder := by
      intro h
      exact B.remainder_nonzero z (zero_dvd_iff.mp (hz ▸ map_dvd ev h))
    have hpProd : p ∣ rationalUnitaryPoleProduct H B.poles :=
      (hprime.dvd_mul.mp (B.factorization ▸ hpb)).resolve_right hnd
    obtain ⟨a, ha, hd⟩ := hprime.dvd_prod_iff.mp hpProd
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
    let root := rationalUnramifiedBasisCoordinateRoot H s.basis (Circle.toUnits s.value)
    have hDvd : p ∣ root := hprime.dvd_of_dvd_pow hd
    have hroot : Prime root :=
      (MulEquiv.prime_iff (rationalUnramifiedBasisLaurentEquiv H s.basis).toMulEquiv).mpr
        (finiteLaurentCoordinateRoot_prime s.dimension (Circle.toUnits s.value))
    let onePole : RationalUnitaryBasisPole H := ⟨s.dimension, s.basis, s.value, 1⟩
    let rootFactors : RationalUnitaryPoleFactorization H root :=
      ⟨[onePole], 1, by
        simp only [rationalUnitaryPoleProduct, onePole, RationalUnitaryBasisPole.factor,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one, mul_one, root],
        fun _ => one_ne_zero⟩
    exact ⟨factorization_of_associated H rootFactors (hprime.associated_of_dvd hroot hDvd).symm⟩)

private theorem nonempty_factorization_prod (s : Multiset R)
    (h : ∀ p ∈ s, Nonempty (RationalUnitaryPoleFactorization H p)) :
    Nonempty (RationalUnitaryPoleFactorization H s.prod) := by
  induction s using Multiset.induction with
  | empty =>
    exact ⟨RationalUnitaryPoleFactorization.ofNonvanishing H 1 (fun _ => one_ne_zero)⟩
  | cons p s ih =>
    obtain ⟨P⟩ := h p (Multiset.mem_cons_self _ _)
    obtain ⟨Q⟩ := ih (fun t ht => h t (Multiset.mem_cons_of_mem ht))
    rw [Multiset.prod_cons]
    exact ⟨P.mul H Q⟩

include hH in
private def factorization_of_prime_support (b : R) (hb : b ≠ 0) (g : R)
    (G : RationalUnitaryPoleFactorization H g)
    (hsupp : ∀ p : R, Prime p → p ∣ b → (∃ z : U, p.val (unitaryToUnramified H z) = 0) → p ∣ g) :
    RationalUnitaryPoleFactorization H b :=
  Classical.choice (by
    classical
    obtain ⟨s, hs, hassoc⟩ := rationalUnramifiedRegularFunctions_exists_prime_factors H hp hH b hb
    have hfactor (p : R) (hps : p ∈ s) : Nonempty (RationalUnitaryPoleFactorization H p) := by
      by_cases h : ∃ z : U, p.val (unitaryToUnramified H z) = 0
      · exact ⟨ofDvdPrime H hH (hs p hps)
          (hsupp p (hs p hps) ((Multiset.dvd_prod hps).trans hassoc.dvd) h) G⟩
      · exact ⟨RationalUnitaryPoleFactorization.ofNonvanishing H p (fun z hz => h ⟨z, hz⟩)⟩
    have hprod := nonempty_factorization_prod H s hfactor
    exact ⟨factorization_of_associated H hprod.some hassoc⟩)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω : Set X} {A : Ω → V →ₗ[ℂ] W}

include hH in
set_option maxHeartbeats 550000 in
private theorem divide_of_zero_fiber
    (q : RationalOperatorContinuationData Ω A)
    (g r : R) (hr : Prime r) (hroot : ∃ z : U, r.val (unitaryToUnramified H z) = 0)
    (hrg : ¬ r ∣ g)
    (hzero : ∀ z : X, g.val z ≠ 0 → r.val z = 0 → q.numerator z = 0) :
    ∃ N : X → V →ₗ[ℂ] W, IsPolynomialOperatorOn Set.univ (fun z => N z.val) ∧
      ∀ z, q.numerator z = r.val z • N z := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  obtain ⟨u, hu⟩ := hroot
  have htest (v : V) (ℓ : Module.Dual ℂ W) :
      ∃ a : R, ∀ z : (Set.univ : Set X), r.val z.val * a.val z.val = ℓ (q.numerator z.val v) := by
    obtain ⟨b, hb⟩ := (isPolynomialOn_scalar_iff _).mp ((q.polynomial v).linearMap ℓ)
    have hd := rationalUnramifiedLocalHypersurfaceDivisibility H hp hH Set.univ r (g * b)
      isOpen_univ hr.irreducible ⟨unitaryToUnramified H u, Set.mem_univ _, hu⟩ (by
        intro z hz hrz
        change g.val z * b.val z = 0
        rcases eq_or_ne (g.val z) 0 with hg | hg
        · rw [hg, zero_mul]
        · have hbz := hb ⟨z, hz⟩
          change ℓ (q.numerator z v) = b.val z at hbz
          rw [hzero z hg hrz, LinearMap.zero_apply, map_zero] at hbz
          rw [← hbz, mul_zero])
    obtain ⟨a, ha⟩ := (hr.dvd_mul.mp hd).resolve_left hrg
    exact ⟨a, fun z => (congrArg (fun f : R => f.val z.val) ha).symm.trans (hb z).symm⟩
  obtain ⟨N, hN, hq⟩ := exists_polynomial_operator_quotient_of_linear_tests r
    (rationalUnramifiedRegular_dense_nonzero_on_open H hp hH r hr.ne_zero isOpen_univ)
    (fun z => q.numerator z.val) q.polynomial htest
  exact ⟨fun z => N ⟨z, Set.mem_univ z⟩, hN, fun z => hq ⟨z, Set.mem_univ z⟩⟩

include hH in
set_option maxHeartbeats 550000 in
private theorem continued_cross_eq (p q : RationalOperatorContinuationData Ω A)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (z : X) :
    p.denominator.val z • q.numerator z = q.denominator.val z • p.numerator z := by
  apply LinearMap.ext
  intro v
  let f : ↥(Set.univ : Set X) → W := fun w =>
    p.denominator.val w.val • q.numerator w.val v - q.denominator.val w.val • p.numerator w.val v
  have hz := rationalUnramifiedPolynomial_eq_zero_of_isOpen H hp hH hΩ hne
    (show Ω ⊆ Set.univ from Set.subset_univ _) f
    (((q.polynomial v).regular_smul p.denominator).sub
      ((p.polynomial v).regular_smul q.denominator)) (by
        intro w hw
        change p.denominator.val w • q.numerator w v - q.denominator.val w • p.numerator w v = 0
        rw [q.clears ⟨w, hw⟩, p.clears ⟨w, hw⟩, LinearMap.smul_apply, LinearMap.smul_apply,
          smul_smul, smul_smul, mul_comm (p.denominator.val w), sub_self])
  exact sub_eq_zero.mp (hz ⟨z, Set.mem_univ z⟩)

include hH in
set_option maxHeartbeats 800000 in
/-- A factored scalar controlling the zero fibers of all cleared numerators
supplies a pole presentation on the original whole operator. -/
def ofClearedZeroFibers (p : RationalOperatorContinuationData Ω A)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (g : R) (G : RationalUnitaryPoleFactorization H g)
    (hzero : ∀ (q : RationalOperatorContinuationData Ω A) (z : X),
      g.val z ≠ 0 → q.denominator.val z = 0 → q.numerator z = 0) :
    RationalOperatorPolePresentation H p.denominator p.numerator :=
  Classical.choice (by
    let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
    let : UniqueFactorizationMonoid R := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid H hp hH
    let S : Set R := {b | ∃ q : RationalOperatorContinuationData Ω A, q.denominator = b}
    obtain ⟨_, ⟨q, rfl⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min S
      ⟨p.denominator, p, rfl⟩
    have hsupport (r : R) (hr : Prime r) (hrb : r ∣ q.denominator)
        (hroot : ∃ z : U, r.val (unitaryToUnramified H z) = 0) : r ∣ g := by
      by_contra hrg
      obtain ⟨b, hb⟩ := hrb
      have hzero' (z : X) (hg : g.val z ≠ 0) (hrz : r.val z = 0) : q.numerator z = 0 :=
        hzero q z hg (by simp only [hb, Subalgebra.coe_mul, Pi.mul_apply, hrz, zero_mul])
      obtain ⟨N, hN, hq⟩ := divide_of_zero_fiber H hH q g r hr hroot hrg hzero'
      have hval (z : Ω) : q.denominator.val z.val = r.val z.val * b.val z.val :=
        congrArg (fun f : R => f.val z.val) hb
      let q' : RationalOperatorContinuationData Ω A := {
        denominator := b
        denominator_nonzero := fun z => right_ne_zero_of_mul ((hval z) ▸ q.denominator_nonzero z)
        numerator := N
        polynomial := hN
        clears := fun z => by
          apply smul_right_injective (V →ₗ[ℂ] W)
            (left_ne_zero_of_mul ((hval z) ▸ q.denominator_nonzero z))
          change r.val z.val • N z.val = r.val z.val • (b.val z.val • A z)
          rw [← hq z.val, q.clears z, hval z, smul_smul] }
      apply hmin b ⟨q', rfl⟩
      exact ⟨q'.denominator_ne_zero hne, r, hr.not_isUnit, hb.trans (mul_comm r b)⟩
    exact ⟨⟨q.denominator, factorization_of_prime_support H hH q.denominator
      (q.denominator_ne_zero hne) g G hsupport, q.numerator, q.polynomial,
      continued_cross_eq H hH p q hΩ hne⟩⟩)

end Langlands.Plancherel.RationalOperatorPolePresentation
