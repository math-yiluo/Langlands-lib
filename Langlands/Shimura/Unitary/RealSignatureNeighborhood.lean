import Langlands.Shimura.Unitary.Signature
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # A neighborhood of a real Hermitian signature matrix -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open Filter
open scoped Matrix.Norms.Operator Topology RightActions

variable (n r : ℕ)

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "J" => signatureMatrix n r

private theorem congruence_expansion (X : M) (hX : star X = X) :
    star (1 + (1 / 2 : ℝ) • (J * X)) * J * (1 + (1 / 2 : ℝ) • (J * X)) =
      J + (X + (1 / 4 : ℝ) • (X * J * X)) := by
  have h₁ : (1 + (1 / 2 : ℝ) • (X * J)) * J = J + (1 / 2 : ℝ) • X := by
    rw [add_mul, one_mul, smul_mul_assoc, mul_assoc, signatureMatrix_sq, mul_one]
  have h₂ : (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X = X := by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  rw [star_add, star_one, star_smul, star_trivial, star_mul, hX, signatureMatrix_star, h₁,
    mul_add, mul_one, mul_smul_comm, add_mul, ← mul_assoc J, signatureMatrix_sq, one_mul,
    smul_mul_assoc, smul_add, smul_smul, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
  rw [← mul_assoc]
  calc
    _ = J + (((1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X) + (1 / 4 : ℝ) • (X * J * X)) := by abel
    _ = _ := by rw [h₂]

/-- Every Hermitian matrix sufficiently close to the signature matrix is
congruent to it by an actual invertible complex matrix. -/
theorem eventually_hermitian_congruent_signature :
    ∀ᶠ H : M in 𝓝 J, star H = H → ∃ P : Mˣ, star (P : M) * J * (P : M) = H := by
  let f (X : M) := X + (1 / 4 : ℝ) • (X * J * X)
  have hf₀ : f 0 = 0 := by simp [f]
  have hfstar (X : M) : f (star X) = star (f X) := by
    simp [f, star_smul, star_mul, signatureMatrix_star, mul_assoc]
  have hf : HasStrictFDerivAt f
      (ContinuousLinearEquiv.refl ℝ M : M →L[ℝ] M) 0 := by
    have h := hasStrictFDerivAt_id (𝕜 := ℝ) (0 : M)
    convert h.add (((h.mul_const' J).mul' h).const_smul (1 / 4 : ℝ)) using 1 <;> try rfl
    apply heq_of_eq
    apply ContinuousLinearMap.ext
    intro Z
    change Z = Z + (1 / 4 : ℝ) • ((0 : M) * J * Z + (Z * J) * 0)
    simp
  let e : OpenPartialHomeomorph M M := hf.toOpenPartialHomeomorph f
  have hs : (0 : M) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  have ht : (0 : M) ∈ e.target := hf₀ ▸ hf.image_mem_toOpenPartialHomeomorph_target
  have h0 : e.symm 0 = 0 := by
    have h := e.left_inv hs
    change e.symm (f 0) = 0 at h
    rwa [hf₀] at h
  have hsymm : Tendsto e.symm (𝓝 0) (𝓝 0) := by
    simpa only [h0] using (e.continuousAt_symm ht).tendsto
  let q (X : M) := 1 + (1 / 2 : ℝ) • (J * X)
  have hq : Continuous fun X => (q X).det := (show Continuous q by dsimp [q]; fun_prop).matrix_det
  have hevq : ∀ᶠ X in 𝓝 (0 : M), (q X).det ≠ 0 :=
    hq.continuousAt.eventually_ne (by simp [q])
  have hstar : Tendsto (fun X : M => star X) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (star : M → M) (0 : M) := continuous_star.continuousAt
    simpa only [star_zero] using h.tendsto
  have heventually : ∀ᶠ y : M in 𝓝 0, y ∈ e.target ∧ e.symm y ∈ e.source ∧
      star (e.symm y) ∈ e.source ∧ (q (e.symm y)).det ≠ 0 :=
    (e.open_target.eventually_mem ht).and ((hsymm.eventually (e.open_source.eventually_mem hs)).and
      (((hstar.comp hsymm).eventually (e.open_source.eventually_mem hs)).and
        (hsymm.eventually hevq)))
  have hsub : Tendsto (fun H : M => H - J) (𝓝 J) (𝓝 0) := by
    have h : ContinuousAt (fun H : M => H - J) J := (continuous_id.sub continuous_const).continuousAt
    simpa only [sub_self] using h.tendsto
  filter_upwards [hsub.eventually heventually] with H hH hself
  let y := H - J
  let X := e.symm y
  have hX : star X = X := by
    apply e.injOn hH.2.2.1 hH.2.1
    change f (star X) = f X
    have hfx : f X = y := e.right_inv hH.1
    rw [hfstar, hfx]
    simp [y, star_sub, hself, signatureMatrix_star]
  let hq' : IsUnit (q X) :=
    (Matrix.isUnit_iff_isUnit_det (q X)).mpr (isUnit_iff_ne_zero.mpr hH.2.2.2)
  refine ⟨hq'.unit, ?_⟩
  rw [hq'.unit_spec, congruence_expansion n r X hX]
  change J + f X = H
  rw [show f X = y from e.right_inv hH.1]
  simp [y]

/-- An open neighborhood whose Hermitian members have the specified signature Gram form. -/
def signatureCongruenceNeighborhood :
    {U : Set M // IsOpen U ∧ J ∈ U ∧ ∀ H ∈ U,
      star H = H → ∃ P : Mˣ, star (P : M) * J * (P : M) = H} := by
  let h := mem_nhds_iff.mp (eventually_hermitian_congruent_signature n r)
  exact ⟨h.choose, h.choose_spec.2.1, h.choose_spec.2.2, fun _ hH => h.choose_spec.1 hH⟩

end Langlands.Shimura.FiniteUnitary
