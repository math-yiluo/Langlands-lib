import Langlands.Representation.Plancherel.RationalUnitaryBasisCancellation
import Langlands.Representation.Plancherel.PolynomialLinearTestBound
import Langlands.Representation.Plancherel.PolynomialOperatorFactorDivision
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus

/-! # One operator denominator after finite unitary basis-root cancellation -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

namespace UnramifiedOperatorFamily

variable {L : Type*} [Group L] [TopologicalSpace L]
  {I : Type*} {ν : I → (L →* ℝ≥0ˣ)}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A polynomial vector numerator is continuous on the whole actual parameter
space in every normed complex carrier. -/
theorem continuous_of_polynomial_univ (f : unramifiedCharacters ν → W)
    (hf : IsPolynomialOn Set.univ (fun z => f z.val)) : Continuous f := by
  obtain ⟨n, a, v, ha⟩ := hf
  have he : f = fun z => ∑ i, (a i).val z • v i :=
    funext (fun z => ha ⟨z, Set.mem_univ _⟩)
  rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_unramifiedRegularFunction ν (a i)).smul continuous_const)

private theorem bound_cancel_continuous_factor
    {Y : Type*} [TopologicalSpace Y]
    (f : Y → W) (r b : Y → ℂ)
    (hf : Continuous f) (hb : Continuous b)
    (hd : Dense {z | r z ≠ 0}) (C : ℝ)
    (hbound : ∀ z, ‖r z • f z‖ ≤ C * ‖r z * b z‖) :
    ∀ z, ‖f z‖ ≤ C * ‖b z‖ := by
  apply norm_le_of_dense f b hf hb _ hd C
  intro z hz
  have hi := hbound z
  simp only [norm_smul, norm_mul] at hi
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
  simpa only [mul_assoc, mul_left_comm] using hi

end UnramifiedOperatorFamily

open UnramifiedOperatorFamily

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance operatorCancellationPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option hygiene false in
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)
set_option hygiene false in
set_option quotPrecheck false in
local notation "X" => unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)

/-- One supplied unitary root factor, with its own integral basis of the
actual valuation image. No root-system or pole-support assertion is built in. -/
structure RationalUnitaryBasisPole where
  dimension : ℕ
  basis : Module.Basis (Fin (dimension + 1)) ℤ Λ
  value : Circle
  multiplicity : ℕ

/-- The actual regular scalar represented by the supplied root power. -/
def RationalUnitaryBasisPole.factor (r : RationalUnitaryBasisPole G) : R :=
  rationalUnramifiedBasisCoordinateRoot G r.basis (Circle.toUnits r.value) ^ r.multiplicity

variable (hG : GroupScheme.IsConnectedReductive G)

include hG in
theorem RationalUnitaryBasisPole.factor_ne_zero (r : RationalUnitaryBasisPole G) :
    r.factor G ≠ 0 := by
  let := rationalUnramifiedRegularFunctions_isDomain G
    (continuous_rationalValuationImageProjection G) hG
  exact pow_ne_zero _ (rationalUnramifiedBasisCoordinateRoot_ne_zero G r.basis r.value)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A cleared operator estimate on the entire actual unitary group. The
constant may depend on the input vector; the denominator is fixed first. -/
def HasClearedUnitaryBound (N : X → V →ₗ[ℂ] W) (b : R) : Prop :=
  ∀ v : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Xu,
    ‖N (unitaryToUnramified G z) v‖ ≤ C * ‖b.val (unitaryToUnramified G z)‖

omit [LocallyOfFiniteType G.X.hom] in
/-- A bound on a dense genuine unitary subset extends to the cleared
polynomial numerator at every unitary point. -/
theorem hasClearedUnitaryBound_of_dense
    (N : X → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (b : R) (D : Set Xu) (hD : Dense D)
    (hbound : ∀ v : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      ‖N (unitaryToUnramified G z) v‖ ≤ C * ‖b.val (unitaryToUnramified G z)‖) :
    HasClearedUnitaryBound G N b := by
  have hu : Continuous (unitaryToUnramified G) :=
    continuous_subtype_val.subtype_mk (fun z => z.property.1)
  intro v
  obtain ⟨C, hC, hbound⟩ := hbound v
  refine ⟨C, hC, norm_le_of_dense
    (fun z : Xu => N (unitaryToUnramified G z) v)
    (fun z : Xu => b.val (unitaryToUnramified G z))
    ((continuous_of_polynomial_univ (fun z => N z v) (hN v)).comp hu)
    ((continuous_unramifiedRegularFunction _ b).comp hu) D hD C hbound⟩

include hG in
/-- A supplied root power divides the entire polynomial operator numerator
whenever it divides its cleared denominator and that numerator has the
specified unitary norm bound. -/
theorem exists_polynomial_operator_quotient_of_unitary_basis_pole
    (r : RationalUnitaryBasisPole G)
    (N : X → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (b : R) (hbound : HasClearedUnitaryBound G N b) (hb : r.factor G ∣ b) :
    ∃ Q : X → V →ₗ[ℂ] W,
      IsPolynomialOperatorOn Set.univ (fun z => Q z.val) ∧
      ∀ z, N z = (r.factor G).val z • Q z := by
  have hd : Dense {z : (Set.univ : Set X) | (r.factor G).val z.val ≠ 0} :=
    rationalUnramifiedRegular_dense_nonzero_on_open G
      (continuous_rationalValuationImageProjection G) hG (r.factor G)
      (r.factor_ne_zero G hG) isOpen_univ
  have hdiv (v : V) (ℓ : W →ₗ[ℂ] ℂ) :
      ∃ a : R, ∀ z : (Set.univ : Set X),
        (r.factor G).val z.val * a.val z.val = ℓ (N z.val v) := by
    obtain ⟨p, hp⟩ := (isPolynomialOn_scalar_iff _).mp ((hN v).linearMap ℓ)
    obtain ⟨C, hC, htest⟩ := (hN v).exists_linear_test_norm_bound ℓ
    obtain ⟨A, hA, hAv⟩ := hbound v
    have hpdiv : r.factor G ∣ p :=
      rationalUnramifiedBasisCoordinateRoot_pow_dvd_of_dense_unitary_bound G
        r.basis r.value r.multiplicity p b Set.univ dense_univ (C * A) (by
          intro z _
          change ‖p.val (unitaryToUnramified G z)‖ ≤
            (C * A) * ‖b.val (unitaryToUnramified G z)‖
          rw [← hp ⟨unitaryToUnramified G z, Set.mem_univ _⟩]
          exact (htest ⟨unitaryToUnramified G z, Set.mem_univ _⟩).trans
            ((mul_le_mul_of_nonneg_left (hAv z) hC).trans_eq (mul_assoc C A _).symm)) hb
    obtain ⟨a, ha⟩ := hpdiv
    refine ⟨a, fun z => ?_⟩
    have he := congrArg (fun t : R => t.val z.val) ha
    change p.val z.val = (r.factor G).val z.val * a.val z.val at he
    exact he.symm.trans (hp z).symm
  obtain ⟨Q, hQ, he⟩ :=
    exists_polynomial_operator_quotient_of_linear_tests (r.factor G) hd
      (fun z : (Set.univ : Set X) => N z.val) hN hdiv
  exact ⟨fun z => Q ⟨z, Set.mem_univ _⟩, hQ, fun z => he ⟨z, Set.mem_univ _⟩⟩

include hG in
/-- Canceling one root power preserves a bound for the remaining denominator,
even at the unitary zeros of the canceled factor. -/
theorem hasClearedUnitaryBound_cancel_basis_pole
    (r : RationalUnitaryBasisPole G)
    (N Q : X → V →ₗ[ℂ] W)
    (hQ : IsPolynomialOperatorOn Set.univ (fun z => Q z.val))
    (b : R) (hbound : HasClearedUnitaryBound G N (r.factor G * b))
    (he : ∀ z, N z = (r.factor G).val z • Q z) :
    HasClearedUnitaryBound G Q b := by
  have hu : Continuous (unitaryToUnramified G) :=
    continuous_subtype_val.subtype_mk (fun z => z.property.1)
  have hd := ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero G hG
    (r.factor G) (r.factor_ne_zero G hG)
  change Dense {z : Xu | (r.factor G).val (unitaryToUnramified G z) ≠ 0} at hd
  intro v
  obtain ⟨C, hC, hbound⟩ := hbound v
  refine ⟨C, hC, ?_⟩
  apply bound_cancel_continuous_factor
    (fun z : Xu => Q (unitaryToUnramified G z) v)
    (fun z : Xu => (r.factor G).val (unitaryToUnramified G z))
    (fun z : Xu => b.val (unitaryToUnramified G z))
    ((continuous_of_polynomial_univ (fun z => Q z v) (hQ v)).comp hu)
    ((continuous_unramifiedRegularFunction _ b).comp hu) hd C
  intro z
  have hi := hbound z
  have hNz : N (unitaryToUnramified G z) v =
      (r.factor G).val (unitaryToUnramified G z) • Q (unitaryToUnramified G z) v :=
    congrArg (fun T : V →ₗ[ℂ] W => T v) (he (unitaryToUnramified G z))
  rw [hNz] at hi
  exact hi

/-- The finite product of the supplied actual root powers. The list and all
its multiplicities are fixed before any vector or scalar test is chosen. -/
def rationalUnitaryPoleProduct (rs : List (RationalUnitaryBasisPole G)) : R :=
  (rs.map (fun r => r.factor G)).prod

include hG in
/-- Remove a finite list of supplied unitary root powers from a whole
polynomial operator numerator. Repeated or associated factors are allowed. -/
theorem exists_polynomial_operator_quotient_of_unitary_pole_list
    (rs : List (RationalUnitaryBasisPole G))
    (N : X → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (d : R)
    (hbound : HasClearedUnitaryBound G N (rationalUnitaryPoleProduct G rs * d)) :
    ∃ Q : X → V →ₗ[ℂ] W,
      IsPolynomialOperatorOn Set.univ (fun z => Q z.val) ∧
      (∀ z, N z = (rationalUnitaryPoleProduct G rs).val z • Q z) ∧
      HasClearedUnitaryBound G Q d := by
  induction rs generalizing N with
  | nil =>
      exact ⟨N, hN, fun z => by simp [rationalUnitaryPoleProduct],
        by simpa only [rationalUnitaryPoleProduct, List.map_nil, List.prod_nil, one_mul] using hbound⟩
  | cons r rs ih =>
      have hprod : rationalUnitaryPoleProduct G (r :: rs) =
          r.factor G * rationalUnitaryPoleProduct G rs := rfl
      have hb : r.factor G ∣ rationalUnitaryPoleProduct G (r :: rs) * d := by
        rw [hprod, mul_assoc]
        exact dvd_mul_right _ _
      obtain ⟨Q₁, hQ₁, he₁⟩ :=
        exists_polynomial_operator_quotient_of_unitary_basis_pole G hG r N hN _ hbound hb
      have hbound₁ : HasClearedUnitaryBound G Q₁ (rationalUnitaryPoleProduct G rs * d) :=
        hasClearedUnitaryBound_cancel_basis_pole G hG r N Q₁ hQ₁ _ (by
          simpa only [hprod, mul_assoc] using hbound) he₁
      obtain ⟨Q, hQ, he, hboundQ⟩ := ih Q₁ hQ₁ hbound₁
      refine ⟨Q, hQ, ?_, hboundQ⟩
      intro z
      calc
        N z = (r.factor G).val z • Q₁ z := he₁ z
        _ = (r.factor G).val z •
            ((rationalUnitaryPoleProduct G rs).val z • Q z) :=
          congrArg (fun T : V →ₗ[ℂ] W => (r.factor G).val z • T) (he z)
        _ = (rationalUnitaryPoleProduct G (r :: rs)).val z • Q z := by
          rw [hprod]
          exact (mul_smul _ _ _).symm

section CancelledOperator

variable
  (rs : List (RationalUnitaryBasisPole G))
  (N : X → V →ₗ[ℂ] W)
  (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
  (d : R)
  (hbound : HasClearedUnitaryBound G N (rationalUnitaryPoleProduct G rs * d))

/-- One polynomial operator obtained by canceling all prescribed root factors
from the original numerator, before choosing any input vector. -/
def rationalUnitaryCancelledOperator : X → V →ₗ[ℂ] W :=
  Classical.choose
    (exists_polynomial_operator_quotient_of_unitary_pole_list G hG rs N hN d hbound)

theorem rationalUnitaryCancelledOperator_isPolynomial :
    IsPolynomialOperatorOn Set.univ
      (fun z => rationalUnitaryCancelledOperator G hG rs N hN d hbound z.val) :=
  (Classical.choose_spec
    (exists_polynomial_operator_quotient_of_unitary_pole_list G hG rs N hN d hbound)).1

theorem rationalUnitaryCancelledOperator_spec (z : X) :
    N z = (rationalUnitaryPoleProduct G rs).val z •
      rationalUnitaryCancelledOperator G hG rs N hN d hbound z :=
  (Classical.choose_spec
    (exists_polynomial_operator_quotient_of_unitary_pole_list G hG rs N hN d hbound)).2.1 z

theorem rationalUnitaryCancelledOperator_bound :
    HasClearedUnitaryBound G
      (rationalUnitaryCancelledOperator G hG rs N hN d hbound) d :=
  (Classical.choose_spec
    (exists_polynomial_operator_quotient_of_unitary_pole_list G hG rs N hN d hbound)).2.2

/-- The regular representative on the nonzero locus of the one remaining
denominator, with values in the same fixed carriers. -/
def rationalUnitaryCancelledQuotient (z : {z : X | d.val z ≠ 0}) : V →ₗ[ℂ] W :=
  (d.val z.val)⁻¹ • rationalUnitaryCancelledOperator G hG rs N hN d hbound z.val

/-- The remaining denominator clears the entire quotient operator on its
regular region, before quantification over the input vector. -/
theorem rationalUnitaryCancelledQuotient_isRational :
    IsRationalOperatorOn {z : X | d.val z ≠ 0}
      (rationalUnitaryCancelledQuotient G hG rs N hN d hbound) := by
  refine ⟨d, fun z => z.property, ?_⟩
  have hp := rationalUnitaryCancelledOperator_isPolynomial G hG rs N hN d hbound
  intro v
  have he :
      (fun z : {z : X | d.val z ≠ 0} =>
        (d.val z.val • rationalUnitaryCancelledQuotient G hG rs N hN d hbound z) v) =
      (fun z : {z : X | d.val z ≠ 0} =>
        rationalUnitaryCancelledOperator G hG rs N hN d hbound z.val v) := by
    funext z
    exact congrArg (fun T : V →ₗ[ℂ] W => T v)
      (smul_inv_smul₀ z.property
        (rationalUnitaryCancelledOperator G hG rs N hN d hbound z.val))
  rw [he]
  exact (hp v).restrict (Set.subset_univ _)

omit [LocallyOfFiniteType G.X.hom] in
theorem isOpen_rationalUnitaryCancelledQuotient_region :
    IsOpen {z : X | d.val z ≠ 0} :=
  isOpen_ne_fun (continuous_unramifiedRegularFunction _ d) continuous_const

end CancelledOperator

end Langlands.Plancherel
