import Langlands.GroupScheme.Quaternionic.QuaternionicPureCongruence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Open congruence orbits of invertible pure quaternion values -/

noncomputable section

universe u

open Filter Topology
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

section Topology

variable {F D R : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [NontriviallyNormedField R] [Algebra F R]
  [TopologicalSpace (R ⊗[F] D)] [IsModuleTopology R (R ⊗[F] D)]

private theorem continuous_reducedNorm :
    Continuous (reducedNorm F D R : R ⊗[F] D → R) := by
  let b := Module.finBasis F D
  change Continuous (fun x => reducedNorm F D R x)
  simp_rw [reducedNorm_eq_polynomialValue F D b, Langlands.ReducedNorm.polynomialValue]
  simp_rw [← MvPolynomial.eval_map]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun i => IsModuleTopology.continuous_of_linearMap ((b.baseChange R).coord i))

end Topology

private theorem eventually_isSquare_sq {R : Type u} [NontriviallyNormedField R]
    [CompleteSpace R] [CharZero R] {r : R} (hr : r ≠ 0) :
    ∀ᶠ z in 𝓝 (r ^ 2), IsSquare z := by
  have hd := (hasStrictDerivAt_pow 2 r).map_nhds_eq (by simpa using mul_ne_zero two_ne_zero hr)
  rw [← hd]
  change ∀ᶠ x in 𝓝 r, IsSquare (x ^ 2)
  apply Filter.Eventually.of_forall
  intro x
  exact ⟨x, pow_two x⟩

/-- In the module topology over a complete nontrivially normed coefficient field,
  all sufficiently close pure values are congruent to an invertible pure value. -/
def QuaternionicPureCongruenceOpenStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [NontriviallyNormedField R] [CompleteSpace R]
    [Algebra F R] [TopologicalSpace (R ⊗[F] D)] [IsModuleTopology R (R ⊗[F] D)]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    ∀ x : (R ⊗[F] D)ˣ, τ (x : R ⊗[F] D) = -↑x →
    ∀ᶠ y in 𝓝 (x : R ⊗[F] D), τ y = -y →
      ∃ u : (R ⊗[F] D)ˣ, (u : R ⊗[F] D) * ↑x * τ u = y

theorem quaternionicPureCongruenceOpen : QuaternionicPureCongruenceOpenStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ _ _ _ _ σ hdim hsym τ x hx
  let A := R ⊗[F] D
  let norm := reducedNorm F D R
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing R A
  let : ContinuousSMul R A := IsModuleTopology.toContinuousSMul R A
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap F R).injective
  have hnorm : Continuous (norm : A → R) := continuous_reducedNorm
  have hxN : norm x ≠ 0 := ((x.isUnit).map norm).ne_zero
  let f : R → R := fun a => a ^ 2
  have hf : HasStrictDerivAt f 2 1 := by simpa [f] using hasStrictDerivAt_pow 2 (1 : R)
  let r := hf.localInverse f 2 1 two_ne_zero
  have hr : r 1 = 1 := by
    have he := (HasStrictDerivAt.eventually_left_inverse hf two_ne_zero).self_of_nhds
    simpa [f, r] using he
  have hrc : ContinuousAt r 1 := by
    simpa only [f, one_pow, r] using (hf.to_localInverse two_ne_zero).hasDerivAt.continuousAt
  have hrEq : ∀ᶠ a in 𝓝 (1 : R), (r a) ^ 2 = a := by
    simpa only [f, one_pow, r] using HasStrictDerivAt.eventually_right_inverse hf two_ne_zero
  let ratio : A → R := fun y => norm y / norm x
  have hratio : Tendsto ratio (𝓝 (x : A)) (𝓝 1) := by
    have h := (hnorm.div_const (norm x)).continuousAt (x := (x : A))
    simpa only [ContinuousAt, ratio, div_self hxN] using h
  let s : A → R := r ∘ ratio
  have hs : Tendsto s (𝓝 (x : A)) (𝓝 1) := by simpa only [hr] using hrc.tendsto.comp hratio
  let g : A → A := fun y => 1 + ((s y)⁻¹ • y) * (↑x⁻¹ : A)
  have hgt : Tendsto g (𝓝 (x : A)) (𝓝 (2 : A)) := by
    have h := (tendsto_const_nhds (x := (1 : A))).add
      (((hs.inv₀ one_ne_zero).smul tendsto_id).mul tendsto_const_nhds (b := (↑x⁻¹ : A)))
    simpa only [g, id_eq, inv_one, one_smul, Units.mul_inv, one_add_one_eq_two] using h
  have hNtwo : norm (2 : A) = (2 : R) ^ 2 := by
    rw [← _root_.map_ofNat (algebraMap R A) 2]
    change reducedNorm F D R ((2 : R) ⊗ₜ[F] (1 : D)) = _
    rw [reducedNorm_scalar, reducedDegree_eq_two_of_finrank_four hdim]
  have hgN : Tendsto (fun y => norm (g y)) (𝓝 (x : A)) (𝓝 ((2 : R) ^ 2)) := by
    rw [← hNtwo]
    exact hnorm.continuousAt.tendsto.comp hgt
  have hdiv := hs.div hgN (pow_ne_zero _ (two_ne_zero : (2 : R) ≠ 0))
  have hsq : ∀ᶠ y in 𝓝 (x : A), IsSquare (s y / norm (g y)) := hdiv.eventually (by
    rw [one_div, ← inv_pow]
    exact eventually_isSquare_sq (inv_ne_zero (two_ne_zero : (2 : R) ≠ 0)))
  filter_upwards [hratio.eventually hrEq, hs.eventually (isOpen_ne.mem_nhds one_ne_zero),
    hgN.eventually (isOpen_ne.mem_nhds (pow_ne_zero _ two_ne_zero)), hsq] with y hy hsy hgy hys hτy
  exact quaternionicPureCongruence F D R σ hdim hsym x y hx hτy (s y) hsy
    ((div_eq_iff hxN).mp hy.symm) hgy hys

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
