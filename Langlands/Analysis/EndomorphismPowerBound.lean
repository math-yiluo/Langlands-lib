import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Basic

/-!
# Common eigenvectors and exponential bounds for powers of endomorphisms

Elementary finite-dimensional complex linear algebra: a commuting family has a
common eigenvector, an eigenvector of every operator of a group representation
defines a character, and powers of an endomorphism whose eigenvalues have
absolute value at most `r₀` grow at most like `c * r ^ m` for every `r > r₀`.
The growth is measured by a fixed submultiplicative size function `endNorm`.
-/

noncomputable section

open Filter
open scoped NNReal ENNReal Topology

namespace Langlands.EndomorphismBound

universe uM uι uA

section CommonEigenvector

variable {ι : Type uι}

/-- Strong induction on the dimension for `exists_common_eigenvector`. -/
theorem exists_common_eigenvector_aux (d : ℕ) :
    ∀ (M : Type uM) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
      (f : ι → Module.End ℂ M), (∀ i j, Commute (f i) (f j)) →
      Module.finrank ℂ M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i v = c • v := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ f hc hd
  by_cases hall : ∀ i, ∃ c : ℂ, ∀ x, f i x = c • x
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    refine ⟨v, hv, fun i => ?_⟩
    obtain ⟨c, hc'⟩ := hall i
    exact ⟨c, hc' v⟩
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f i)
  let W : Submodule ℂ M := (f i).eigenspace μ
  have hW : ∀ j, ∀ w ∈ W, f j w ∈ W := by
    intro j w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    calc f i (f j w) = (f i * f j) w := rfl
      _ = (f j * f i) w := by rw [(hc i j).eq]
      _ = f j (μ • w) := by rw [Module.End.mul_apply, hw]
      _ = μ • f j w := map_smul _ _ _
  have hWbot : W ≠ ⊥ := hμ
  have hWtop : W ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hi μ
    have hxW : x ∈ W := h ▸ Submodule.mem_top
    exact hx ((Module.End.mem_eigenspace_iff).mp hxW)
  have hlt : Module.finrank ℂ W < d :=
    hd ▸ Submodule.finrank_lt hWtop
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
  let g : ι → Module.End ℂ W := fun j => (f j).restrict (hW j)
  have hcg : ∀ j l, Commute (g j) (g l) := by
    intro j l
    refine LinearMap.ext fun w => Subtype.ext ?_
    change f j (f l w) = f l (f j w)
    exact LinearMap.congr_fun (hc j l).eq (w : M)
  obtain ⟨w, hw0, hw⟩ := ih _ hlt W g hcg rfl
  refine ⟨w, fun h => hw0 (Subtype.ext h), fun j => ?_⟩
  obtain ⟨c, hcw⟩ := hw j
  exact ⟨c, congrArg Subtype.val hcw⟩

/-- A commuting family of endomorphisms of a nonzero finite-dimensional complex
vector space has a common eigenvector. -/
theorem exists_common_eigenvector {M : Type uM} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (f : ι → Module.End ℂ M)
    (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i v = c • v :=
  exists_common_eigenvector_aux _ M f hc rfl

end CommonEigenvector

section Character

/-- A nonzero vector that is an eigenvector of every operator of a group
representation determines a character, its eigenvalue function. -/
theorem exists_character_of_forall_eigen {A : Type uA} [Group A]
    {X : Type uM} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ A X) {w : X}
    (hw : w ≠ 0) (h : ∀ a, ∃ c : ℂ, π a w = c • w) :
    ∃ χ : A →* ℂˣ, ∀ a, π a w = (χ a : ℂ) • w := by
  choose c hc using h
  have hinj : ∀ x y : ℂ, x • w = y • w → x = y := fun x y hxy =>
    smul_left_injective ℂ hw hxy
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hinj
    rw [← hc, map_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul, mul_comm]
  have hone : c 1 = 1 := by
    apply hinj
    rw [← hc, map_one, Module.End.one_apply, one_smul]
  let χ₀ : A →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  exact ⟨χ₀.toHomUnits, fun a => hc a⟩

end Character

section PowerBound

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {W : Type uM} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- A fixed submultiplicative size of an endomorphism: the `L¹-L∞` operator norm of
its matrix in the standard finite basis. -/
def endNorm (f : Module.End ℂ W) : ℝ :=
  ‖LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ W) f‖

theorem endNorm_nonneg (f : Module.End ℂ W) : 0 ≤ endNorm f :=
  norm_nonneg _

theorem endNorm_mul_le (f g : Module.End ℂ W) :
    endNorm (f * g) ≤ endNorm f * endNorm g := by
  unfold endNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- Powers of a complex matrix whose spectrum lies in the closed disc of radius
`r₀` grow at most like `c * r ^ m` for every `r > r₀`. -/
theorem matrix_pow_bound {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) {r₀ r : ℝ}
    (hr₀ : 0 ≤ r₀) (hr : r₀ < r) (hspec : ∀ μ ∈ spectrum ℂ X, ‖μ‖ ≤ r₀) :
    ∃ c : ℝ, ∀ m : ℕ, ‖X ^ m‖ ≤ c * r ^ m := by
  have : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℂ _
  have hrpos : 0 < r := hr₀.trans_lt hr
  have hrad : spectralRadius ℂ X ≤ ENNReal.ofReal r₀ := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun μ hμ => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by simpa using hspec μ hμ)
  have hlt : limsup (fun n : ℕ => (‖X ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop <
      ENNReal.ofReal r :=
    ((spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius X).trans hrad).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hr)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hlt)
  have hbig : ∀ n, N + 1 ≤ n → ‖X ^ n‖ ≤ r ^ n := by
    intro n hn
    have h1 := hN n (by omega)
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    have h2 : (‖X ^ n‖₊ : ℝ≥0∞) < ENNReal.ofReal r ^ n := by
      have h3 := ENNReal.rpow_lt_rpow h1 (show (0 : ℝ) < n by positivity)
      rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast] at h3
    rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h2
    exact h2.le
  refine ⟨∑ k ∈ Finset.range (N + 1), ‖X ^ k‖ / r ^ k + 1, fun m => ?_⟩
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖X ^ k‖ / r ^ k :=
    Finset.sum_nonneg fun k _ => by positivity
  by_cases hm : m ≤ N
  · have hterm : ‖X ^ m‖ / r ^ m ≤ ∑ k ∈ Finset.range (N + 1), ‖X ^ k‖ / r ^ k :=
      Finset.single_le_sum (f := fun k => ‖X ^ k‖ / r ^ k) (fun k _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    have hrm : 0 < r ^ m := by positivity
    calc ‖X ^ m‖ = ‖X ^ m‖ / r ^ m * r ^ m := by field_simp
      _ ≤ (∑ k ∈ Finset.range (N + 1), ‖X ^ k‖ / r ^ k + 1) * r ^ m := by
        apply mul_le_mul_of_nonneg_right _ hrm.le
        linarith
  · calc ‖X ^ m‖ ≤ r ^ m := hbig m (by omega)
      _ = 1 * r ^ m := (one_mul _).symm
      _ ≤ (∑ k ∈ Finset.range (N + 1), ‖X ^ k‖ / r ^ k + 1) * r ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

/-- Powers of an endomorphism whose eigenvalues have absolute value at most `r₀`
grow at most like `c * r ^ m` for every `r > r₀`. -/
theorem exists_endNorm_pow_le (f : Module.End ℂ W) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r)
    (hev : ∀ (μ : ℂ) (x : W), x ≠ 0 → f x = μ • x → ‖μ‖ ≤ r₀) :
    ∃ c : ℝ, ∀ m : ℕ, endNorm (f ^ m) ≤ c * r ^ m := by
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ W)
  obtain ⟨c, hc⟩ := matrix_pow_bound (e f) hr₀ hr (by
    intro μ hμ
    rw [AlgEquiv.spectrum_eq] at hμ
    obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
    exact hev μ x hx.2 hx.apply_eq_smul)
  refine ⟨c, fun m => ?_⟩
  unfold endNorm
  rw [map_pow]
  exact hc m

/-- Evaluating a fixed functional at the image of a fixed vector is bounded by a
constant multiple of `endNorm`. -/
theorem exists_apply_le_endNorm (φ : Module.Dual ℂ W) (v : W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Module.End ℂ W, ‖φ (f v)‖ ≤ C * endNorm f := by
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ W)
  let L : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ →ₗ[ℂ] ℂ :=
    φ ∘ₗ (LinearMap.applyₗ v) ∘ₗ e.symm.toLinearEquiv.toLinearMap
  let Lc := LinearMap.toContinuousLinearMap L
  obtain ⟨C, hC0, hC⟩ := Lc.bound
  refine ⟨C, hC0.le, fun f => ?_⟩
  have h := hC (e f)
  have hL : Lc (e f) = φ (f v) := by
    change φ ((e.symm (e f)) v) = φ (f v)
    rw [AlgEquiv.symm_apply_apply]
  have h' : ‖φ (f v)‖ ≤ C * ‖e f‖ := by
    convert h using 2
    exact hL.symm
  exact h'

end PowerBound

end Langlands.EndomorphismBound
