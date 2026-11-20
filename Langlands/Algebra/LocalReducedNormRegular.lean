import Langlands.Algebra.ReducedCharpolyRegularElements
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Regular representatives in local reduced-norm fibers -/

noncomputable section

universe u

open Filter Topology
open scoped TensorProduct

namespace Langlands.CentralSimple

variable {K A : Type u} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
  [Ring A] [Algebra K A] [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

omit [CompleteSpace K] [CharZero K] in
private theorem reducedNorm_eq_eval_coordinates {J : Type u} [Fintype J]
    (b : Module.Basis J K A) (c : J → K) :
    reducedNorm K A K (1 ⊗ₜ[K] ∑ j, c j • b j) =
      MvPolynomial.eval c (reducedNormPolynomial K A b) := by
  classical
  rw [reducedNorm_eq_polynomialValue K A b, Langlands.ReducedNorm.polynomialValue,
    Algebra.algebraMap_self, MvPolynomial.eval₂_id]
  have hc : (fun j => (b.baseChange K).repr (1 ⊗ₜ[K] ∑ i, c i • b i) j) = c := by
    funext j
    rw [Module.Basis.baseChange_repr_tmul, smul_eq_mul, mul_one, b.repr_sum_self]
  exact congrArg (fun x => MvPolynomial.eval x (reducedNormPolynomial K A b)) hc

omit [CompleteSpace K] [CharZero K] in
private theorem reducedNorm_smul_original (s : K) (z : A) :
    reducedNorm K A K (1 ⊗ₜ[K] (s • z)) =
      s ^ reducedDegree K A * reducedNorm K A K (1 ⊗ₜ[K] z) := by
  have h : (1 : K) ⊗ₜ[K] (s • z) = (s ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] z) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.smul_tmul]
    simp
  rw [h, map_mul, reducedNorm_scalar]

/-- An element of nonzero reduced norm over a complete nontrivially normed field of
characteristic zero can be replaced by an element of the same norm with separable reduced
characteristic polynomial. -/
theorem exists_norm_eq_with_separable_reducedCharpoly (a : A)
    (ha : reducedNorm K A K (1 ⊗ₜ[K] a) ≠ 0) :
    ∃ z : A, reducedNorm K A K (1 ⊗ₜ[K] z) = reducedNorm K A K (1 ⊗ₜ[K] a) ∧
      (reducedCharpoly K A z).Separable := by
  classical
  let n := reducedDegree K A
  let J := ULift.{u} (Fin (Module.finrank K A))
  let b : Module.Basis J K A := (Module.finBasis K A).reindex Equiv.ulift.symm
  let p := reducedNormPolynomial K A b
  let q : J → K := fun i => b.repr a i
  let N := reducedNorm K A K (1 ⊗ₜ[K] a)
  let f (x : J → K) : K := MvPolynomial.eval x p / N
  have hq : f q = 1 := by
    change MvPolynomial.eval q (reducedNormPolynomial K A b) / N = 1
    rw [← reducedNorm_eq_eval_coordinates (J := J) b q,
      show (∑ i, q i • b i) = a from b.sum_repr a,
      div_self ha]
  have hcont : Continuous f := (MvPolynomial.continuous_eval p).div_const N
  let powers := Set.range (fun s : Kˣ => s ^ n)
  have hn : n ≠ 0 := (reducedDegree_pos K A).ne'
  have hp : powers ∈ 𝓝 (1 : Kˣ) := Langlands.Global.AdelicFunctoriality.range_pow_mem_nhds_one hn
  have himage : (Units.val : Kˣ → K) '' powers ∈ 𝓝 (1 : K) := by
    rw [← Units.val_one, ← IsOpenUnits.isOpenEmbedding_unitsVal.map_nhds_eq]
    exact Filter.image_mem_map hp
  have hpre := hcont.continuousAt.preimage_mem_nhds (hq.symm ▸ himage)
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨I, S, hS, hbox⟩ := hpre
  obtain ⟨x, hx, hreg⟩ := exists_separable_reducedCharpoly_in_basis_box b S
    (fun i => infinite_of_mem_nhds (q i) (hS i))
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hbox (fun i _ => hx i)
  let y := ∑ i, x i • b i
  have hy : reducedNorm K A K (1 ⊗ₜ[K] y) = (s : K) ^ n * N := by
    have hh : (s : K) ^ n = reducedNorm K A K (1 ⊗ₜ[K] y) / N := by
      rw [reducedNorm_eq_eval_coordinates (J := J) b x]
      simpa only [f, p, Units.val_pow_eq_pow_val] using hs
    exact (eq_div_iff ha).mp hh |>.symm
  refine ⟨(s : K)⁻¹ • y, ?_, reducedCharpoly_separable_smul (inv_ne_zero s.ne_zero) hreg⟩
  rw [reducedNorm_smul_original, hy, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n s.ne_zero),
    one_mul]

/-- Every nonzero reduced-norm fiber has a regular representative over a complete
nontrivially normed field of characteristic zero. -/
def LocalReducedNormRegularStatement : Prop :=
  ∀ (K A : Type u) [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (a : A), reducedNorm K A K (1 ⊗ₜ[K] a) ≠ 0 →
      ∃ z : A, reducedNorm K A K (1 ⊗ₜ[K] z) = reducedNorm K A K (1 ⊗ₜ[K] a) ∧
        (reducedCharpoly K A z).Separable

/-- The local regular representative follows by a scalar adjustment near one. -/
theorem localReducedNormRegular : LocalReducedNormRegularStatement.{u} := by
  intro K A _ _ _ _ _ _ _ _ a ha
  exact exists_norm_eq_with_separable_reducedCharpoly a ha

end Langlands.CentralSimple
