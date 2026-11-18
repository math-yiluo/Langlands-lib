import Langlands.Representation.Plancherel.RationalUnramifiedVectorCancellation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Whole-operator polynomial division from scalar tests -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open scoped NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe uG uI uV uW

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Set (unramifiedCharacters ν)}

/-- Every scalar algebraic linear test of a polynomial vector family is
continuous; no topology on the vector carrier is required. -/
theorem IsPolynomialOn.continuous_linear_test
    {f : U → W} (hf : IsPolynomialOn U f) (ℓ : W →ₗ[ℂ] ℂ) :
    Continuous (fun z => ℓ (f z)) := by
  obtain ⟨a, ha⟩ := (isPolynomialOn_scalar_iff _).mp (hf.linearMap ℓ)
  have he : (fun z => ℓ (f z)) = (fun z : U => a.val z.val) := funext ha
  rw [he]
  exact (continuous_unramifiedRegularFunction ν a).comp continuous_subtype_val

/-- Scalar multiplication by a regular function with dense nonzero locus is
injective on polynomial vector families, without a topology on their carrier. -/
theorem polynomial_eq_of_regular_smul_eq
    (d : unramifiedRegularFunctions ν)
    (hd : Dense {z : U | d.val z.val ≠ 0})
    {f g : U → W} (hf : IsPolynomialOn U f) (hg : IsPolynomialOn U g)
    (he : ∀ z, d.val z.val • f z = d.val z.val • g z) :
    f = g := by
  have hs (ℓ : W →ₗ[ℂ] ℂ) : (fun z => ℓ (f z)) = (fun z => ℓ (g z)) := by
    apply Continuous.ext_on hd (hf.continuous_linear_test ℓ) (hg.continuous_linear_test ℓ)
    intro z hz
    apply mul_left_cancel₀ hz
    simpa only [map_smul, smul_eq_mul] using congrArg ℓ (he z)
  funext z
  apply Module.eval_apply_injective ℂ
  ext ℓ
  exact congrFun (hs ℓ) z

/-- If each scalar linear test of a polynomial vector numerator has the same
regular factor, the entire vector numerator has a polynomial quotient. -/
theorem exists_polynomial_quotient_of_linear_tests
    (d : unramifiedRegularFunctions ν) (f : U → W) (hf : IsPolynomialOn U f)
    (hdiv : ∀ ℓ : W →ₗ[ℂ] ℂ,
      ∃ a : unramifiedRegularFunctions ν, ∀ z : U,
        d.val z.val * a.val z.val = ℓ (f z)) :
    ∃ g : U → W, IsPolynomialOn U g ∧ ∀ z, f z = d.val z.val • g z := by
  classical
  obtain ⟨n, b, v, hnum⟩ := hf
  let S : Submodule ℂ W := Submodule.span ℂ (Set.range v)
  let := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hv (i : Fin n) : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hmem (z : U) : f z ∈ S := by
    rw [hnum z]
    exact S.sum_mem (fun i hi => S.smul_mem _ (hv i))
  let fS : U → S := fun z => ⟨f z, hmem z⟩
  let T : W →ₗ[ℂ] S := S.subtype.leftInverse
  have hT (w : S) : T (w : W) = w :=
    S.subtype.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr Subtype.val_injective) w
  have hTf (z : U) : T (f z) = fS z := hT (fS z)
  let e := Module.finBasis ℂ S
  have hcoord (i : Fin (Module.finrank ℂ S)) :
      ∃ a : unramifiedRegularFunctions ν, ∀ z : U,
        d.val z.val * a.val z.val = e.repr (fS z) i := by
    obtain ⟨a, ha⟩ := hdiv ((e.coord i).comp T)
    refine ⟨a, ?_⟩
    intro z
    have hi := ha z
    rw [LinearMap.comp_apply, hTf] at hi
    exact hi
  choose a ha using hcoord
  let g : U → W := fun z => ∑ i, (a i).val z.val • ((e i : S) : W)
  refine ⟨g, ⟨Module.finrank ℂ S, a, fun i => ((e i : S) : W), fun z => rfl⟩, ?_⟩
  intro z
  have he := congrArg (fun s : S => (s : W)) (e.sum_repr (fS z))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  calc
    f z = ∑ i, e.repr (fS z) i • ((e i : S) : W) := he.symm
    _ = ∑ i, d.val z.val • ((a i).val z.val • ((e i : S) : W)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← ha i z, mul_smul]
    _ = d.val z.val • g z := Finset.smul_sum.symm

/-- One regular scalar factor divides a whole polynomial operator whenever
it divides all scalar tests of all input vectors. The quotient remains linear
in the input, and the factor is fixed before any input vector is chosen. -/
theorem exists_polynomial_operator_quotient_of_linear_tests
    (d : unramifiedRegularFunctions ν)
    (hd : Dense {z : U | d.val z.val ≠ 0})
    (N : U → V →ₗ[ℂ] W) (hN : IsPolynomialOperatorOn U N)
    (hdiv : ∀ (v : V) (ℓ : W →ₗ[ℂ] ℂ),
      ∃ a : unramifiedRegularFunctions ν, ∀ z : U,
        d.val z.val * a.val z.val = ℓ (N z v)) :
    ∃ Q : U → V →ₗ[ℂ] W, IsPolynomialOperatorOn U Q ∧
      ∀ z, N z = d.val z.val • Q z := by
  classical
  choose g hg hmul using fun v =>
    exists_polynomial_quotient_of_linear_tests d (fun z => N z v) (hN v) (hdiv v)
  have hadd (v w : V) : g (v + w) = fun z => g v z + g w z := by
    apply polynomial_eq_of_regular_smul_eq d hd (hg (v + w)) ((hg v).add (hg w))
    intro z
    rw [← hmul, smul_add, ← hmul, ← hmul, map_add]
  have hsmul (c : ℂ) (v : V) : g (c • v) = fun z => c • g v z := by
    have hpoly : IsPolynomialOn U (fun z => c • g v z) := by
      simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
        (hg v).linearMap (c • (LinearMap.id : W →ₗ[ℂ] W))
    apply polynomial_eq_of_regular_smul_eq d hd (hg (c • v)) hpoly
    intro z
    rw [← hmul, smul_comm, ← hmul, map_smul]
  let Q : U → V →ₗ[ℂ] W := fun z =>
    { toFun := fun v => g v z
      map_add' := fun v w => congrFun (hadd v w) z
      map_smul' := fun c v => congrFun (hsmul c v) z }
  refine ⟨Q, fun v => hg v, ?_⟩
  intro z
  ext v
  exact hmul v z

section Quotient

variable (d : unramifiedRegularFunctions ν)
  (hd : Dense {z : U | d.val z.val ≠ 0})
  (N : U → V →ₗ[ℂ] W) (hN : IsPolynomialOperatorOn U N)
  (hdiv : ∀ (v : V) (ℓ : W →ₗ[ℂ] ℂ),
    ∃ a : unramifiedRegularFunctions ν, ∀ z : U,
      d.val z.val * a.val z.val = ℓ (N z v))

/-- The whole polynomial operator quotient by one fixed regular factor,
constructed from scalar-test divisibility and polynomial uniqueness. -/
def polynomialOperatorFactorQuotient : U → V →ₗ[ℂ] W :=
  Classical.choose
    (exists_polynomial_operator_quotient_of_linear_tests d hd N hN hdiv)

/-- Each fixed input of the constructed quotient has a finite polynomial
expansion. -/
theorem polynomialOperatorFactorQuotient_isPolynomial :
    IsPolynomialOperatorOn U (polynomialOperatorFactorQuotient d hd N hN hdiv) :=
  (Classical.choose_spec
    (exists_polynomial_operator_quotient_of_linear_tests d hd N hN hdiv)).1

/-- The constructed quotient satisfies the same factor identity as a whole
operator at every parameter. -/
theorem polynomialOperatorFactorQuotient_spec (z : U) :
    N z = d.val z.val • polynomialOperatorFactorQuotient d hd N hN hdiv z :=
  (Classical.choose_spec
    (exists_polynomial_operator_quotient_of_linear_tests d hd N hN hdiv)).2 z

end Quotient

end Langlands.Plancherel.UnramifiedOperatorFamily
