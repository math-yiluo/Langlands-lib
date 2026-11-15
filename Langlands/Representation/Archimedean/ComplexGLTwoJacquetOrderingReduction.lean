import Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrdering
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueReduction
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# Reduction of the `GL_2(ℂ)` ordering of Jacquet exponents to moment integrals

This file reduces `ComplexGLTwoJacquetOrderingStatement` to two statements about the
principal series `X(d)` of `GL_2(ℂ)` (the `U(2)`-finite functions of the standard module of
two complex characters `d 0`, `d 1`). Write `w = [[0, 1], [1, 0]]`, `n(z) = [[1, z], [0, 1]]`,
and let the moments be

`M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz`.

* `ComplexGLTwoMomentJacquetStatement`: for `i + j < 2 Re(t_0 - t_1)` (`t_k` the exponent
  of `d k`) the integrand is integrable on `X(d)`, the upper nilpotent direction lowers the
  indices, and the diagonal acts on `M_{i,j}` by explicit scalars.
* `ComplexGLTwoMomentCompletenessStatement`: if `Re t_1 < Re t_0`, every nonzero
  `(𝔤, K)`-submodule of `X(d)` contains `f` with `M_{i,j} f ≠ 0` for some
  `i + j ≤ Re(t_0 - t_1)`.

`ComplexGLTwoJacquetOrderingReductionStatement` says these two statements imply
`ComplexGLTwoJacquetOrderingStatement`, and `complexGLTwoJacquetOrderingReduction` proves
it, using Frobenius reciprocity (`complexJacquetFrobenius`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## The moments -/

/-- The long Weyl element `w = [[0, 1], [1, 0]]` of `GL_2(ℂ)`. -/
def complexGLTwoWeyl : Langlands.GeneralLinear 2 ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

/-- The upper unipotent element `n(z) = [[1, z], [0, 1]]` of `GL_2(ℂ)`. -/
def complexGLTwoUnipotent (z : ℂ) : Langlands.GeneralLinear 2 ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, z; 0, 1] (by simp [Matrix.det_fin_two])

/-- The moment `M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz` of a function `f` on `GL_2(ℂ)`, for
Lebesgue measure on `ℂ`. (The Bochner integral is `0` when the integrand is not
integrable.) -/
def complexGLTwoMoment (i j : ℕ) (f : Langlands.GeneralLinear 2 ℂ → ℂ) : ℂ :=
  ∫ z : ℂ, f (complexGLTwoWeyl * complexGLTwoUnipotent z) * z ^ i * (starRingEnd ℂ z) ^ j

/-- The moments are Jacquet-type functionals on the principal series. Let `d 0`, `d 1` be
complex characters with exponents `t_0`, `t_1` and weights `l_0`, `l_1`, let
`f ∈ X(d)` and `i + j < 2 Re(t_0 - t_1)`. Then `z ↦ f(w n(z)) z^i z̄^j` is integrable;
for `X` strictly upper triangular,
`M_{i,j}(R(X) f) = -(i X₀₁ M_{i-1,j} f + j X̄₀₁ M_{i,j-1} f)`;
and `M_{i,j}(R(E_kk) f) = a'_k M_{i,j} f`, `M_{i,j}(R(i E_kk) f) = b'_k M_{i,j} f` with
`a' = (2 t_1 + 1 + (i + j), 2 t_0 - 1 - (i + j))` and
`b' = (i (l_1 + i - j), i (l_0 - i + j))`. Here `R(X)` is the right derivative. -/
def ComplexGLTwoMomentJacquetStatement : Prop :=
  ∀ (d : Fin 2 → ComplexCharacterData) (i j : ℕ),
    ((i + j : ℕ) : ℝ) < 2 * ((d 0).exponent.re - (d 1).exponent.re) →
    ∀ f ∈ kFiniteFunctions (complexStandardModule 2 (List.ofFn d)) (unitaryCompact ℂ 2),
      MeasureTheory.Integrable (fun z : ℂ =>
          f (complexGLTwoWeyl * complexGLTwoUnipotent z) * z ^ i * (starRingEnd ℂ z) ^ j) ∧
      (∀ X : Matrix (Fin 2) (Fin 2) ℂ, (∀ a b : Fin 2, (b : ℕ) ≤ a → X a b = 0) →
        complexGLTwoMoment i j (rightDerivative (matrixModel ℂ 2) X f) =
          -((i : ℂ) * X 0 1 * complexGLTwoMoment (i - 1) j f +
            (j : ℂ) * starRingEnd ℂ (X 0 1) * complexGLTwoMoment i (j - 1) f)) ∧
      ∀ k : Fin 2,
        complexGLTwoMoment i j (rightDerivative (matrixModel ℂ 2) (Matrix.single k k 1) f) =
            ![2 * (d 1).exponent + 1 + ((i + j : ℕ) : ℂ),
              2 * (d 0).exponent - 1 - ((i + j : ℕ) : ℂ)] k * complexGLTwoMoment i j f ∧
          complexGLTwoMoment i j
              (rightDerivative (matrixModel ℂ 2) (Matrix.single k k Complex.I) f) =
            ![Complex.I * (((d 1).weight : ℂ) + (i : ℂ) - (j : ℂ)),
              Complex.I * (((d 0).weight : ℂ) - (i : ℂ) + (j : ℂ))] k *
              complexGLTwoMoment i j f

/-- Nonvanishing of low moments on submodules. Let `d 0`, `d 1` be complex characters with
exponents `t_0`, `t_1` and `Re t_1 < Re t_0`. Every nonzero `(𝔤, K)`-submodule `S` of the
`U(2)`-finite principal series `X(d)` contains a function `f` with `M_{i,j} f ≠ 0` for some
`i + j ≤ Re(t_0 - t_1)`. -/
def ComplexGLTwoMomentCompletenessStatement : Prop :=
  ∀ d : Fin 2 → ComplexCharacterData, (d 1).exponent.re < (d 0).exponent.re →
    ∀ S : Submodule ℂ
        (kFiniteFunctions (complexStandardModule 2 (List.ofFn d)) (unitaryCompact ℂ 2)),
      IsGKSubmodule (complexStandardRep 2 (List.ofFn d)) (complexStandardLie 2 (List.ofFn d))
          S →
        S ≠ ⊥ →
          ∃ (i j : ℕ) (f : kFiniteFunctions (complexStandardModule 2 (List.ofFn d))
              (unitaryCompact ℂ 2)),
            f ∈ S ∧ ((i + j : ℕ) : ℝ) ≤ (d 0).exponent.re - (d 1).exponent.re ∧
              complexGLTwoMoment i j (f : Langlands.GeneralLinear 2 ℂ → ℂ) ≠ 0

/-- The moment statements imply the ordering of Jacquet exponents for
`(𝔤𝔩_2(ℂ), U(2))`-modules. -/
def ComplexGLTwoJacquetOrderingReductionStatement : Prop :=
  ComplexGLTwoMomentJacquetStatement → ComplexGLTwoMomentCompletenessStatement →
    ComplexGLTwoJacquetOrderingStatement.{uV}

/-! ## Linearity of a convergent moment -/

section Linear

variable (d : Fin 2 → ComplexCharacterData) (i j : ℕ)

/-- A convergent moment as a linear functional on `X(d)`. -/
def complexGLTwoMomentLinear (hM : ComplexGLTwoMomentJacquetStatement)
    (hij : ((i + j : ℕ) : ℝ) < 2 * ((d 0).exponent.re - (d 1).exponent.re)) :
    kFiniteFunctions (complexStandardModule 2 (List.ofFn d)) (unitaryCompact ℂ 2) →ₗ[ℂ] ℂ where
  toFun f := complexGLTwoMoment i j (f : Langlands.GeneralLinear 2 ℂ → ℂ)
  map_add' f g := by
    have hf := (hM d i j hij f f.2).1
    have hg := (hM d i j hij g g.2).1
    unfold complexGLTwoMoment
    rw [← MeasureTheory.integral_add hf hg]
    congr 1
    funext z
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c f := by
    unfold complexGLTwoMoment
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext z
    ring

theorem complexGLTwoMomentLinear_apply (hM : ComplexGLTwoMomentJacquetStatement)
    (hij : ((i + j : ℕ) : ℝ) < 2 * ((d 0).exponent.re - (d 1).exponent.re))
    (f : kFiniteFunctions (complexStandardModule 2 (List.ofFn d)) (unitaryCompact ℂ 2)) :
    complexGLTwoMomentLinear d i j hM hij f =
      complexGLTwoMoment i j (f : Langlands.GeneralLinear 2 ℂ → ℂ) := rfl

end Linear

/-! ## The image of an embedding is a `(𝔤, K)`-submodule -/

section Image

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin 2) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {cs : List ComplexCharacterData}
  {E : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule 2 cs) (unitaryCompact ℂ 2)}

/-- The range of an embedding into a standard module is a `(𝔤, K)`-submodule. -/
theorem IsComplexStandardEmbedding.isGKSubmodule_range
    (hE : IsComplexStandardEmbedding 2 ρ π cs E) :
    IsGKSubmodule (complexStandardRep 2 cs) (complexStandardLie 2 cs) (LinearMap.range E) := by
  refine ⟨?_, ?_⟩
  · rintro k _ ⟨v, rfl⟩
    exact ⟨ρ k v, hE.map_rep k v⟩
  · intro X
    induction X using TensorProduct.inductionOn with
    | tmul c M =>
      rintro _ ⟨v, rfl⟩
      have hcM : (c ⊗ₜ[ℝ] M : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) = c • (1 ⊗ₜ M) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcM, map_smul, LinearMap.smul_apply]
      exact (LinearMap.range E).smul_mem c ⟨π (1 ⊗ₜ M) v, hE.map_lie_one_tmul M v⟩
    | add X Y hX hY =>
      intro w hw
      rw [map_add, LinearMap.add_apply]
      exact (LinearMap.range E).add_mem (hX w hw) (hY w hw)

end Image

/-! ## The reduction -/

/-- Proof of the reduction. Frobenius reciprocity gives characters `d` and a nonzero
embedding `B : V → X(d)`, with `a = (2 t_0 + 1, 2 t_1 - 1)`. If `Re t_0 ≤ Re t_1` the
functional `ℓ` is already ordered. Otherwise the range of `B` is a nonzero
`(𝔤, K)`-submodule, so some moment `M_{i,j}` with `i + j ≤ Re(t_0 - t_1)` is nonzero on it;
take `i + j` minimal. Then `v ↦ M_{i,j}(B v)` is linear (the integrals converge), killed by
the upper nilpotent direction (the lower moments vanish on the range by minimality), and
has exponents `a' = (2 t_1 + 1 + (i + j), 2 t_0 - 1 - (i + j))`, which have the same sum as
`a` and satisfy `Re a'_0 ≤ Re a'_1 + 2`. -/
theorem complexGLTwoJacquetOrderingReduction :
    ComplexGLTwoJacquetOrderingReductionStatement.{uV} := by
  intro hM hC V _ _ ρ π hgk ℓ a b hℓ hJ
  obtain ⟨d, hda, hdb, B, hB, hBemb⟩ := complexJacquetFrobenius 2 V ρ π hgk ℓ a b hℓ hJ
  have ha0 : a 0 = 2 * (d 0).exponent + 1 := by
    rw [← hda 0]
    simp only [Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]
    ring
  have ha1 : a 1 = 2 * (d 1).exponent - 1 := by
    rw [← hda 1]
    simp only [Fin.val_one, Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hle : (d 0).exponent.re ≤ (d 1).exponent.re
  · refine ⟨ℓ, a, b, hℓ, hJ, rfl, ?_⟩
    rw [ha0, ha1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.one_re]
    norm_num
    linarith
  push Not at hle
  set s : ℝ := (d 0).exponent.re - (d 1).exponent.re with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  obtain ⟨i₁, j₁, f₁, hf₁, hr₁, hne₁⟩ :=
    hC d hle (LinearMap.range B) hBemb.isGKSubmodule_range
      (by rwa [Ne, LinearMap.range_eq_bot])
  have hex : ∃ k : ℕ, ∃ (i j : ℕ) (v : V), i + j = k ∧ ((i + j : ℕ) : ℝ) ≤ s ∧
      complexGLTwoMoment i j (B v : Langlands.GeneralLinear 2 ℂ → ℂ) ≠ 0 := by
    obtain ⟨v, rfl⟩ := hf₁
    exact ⟨i₁ + j₁, i₁, j₁, v, rfl, hr₁, hne₁⟩
  classical
  obtain ⟨i₀, j₀, v₀, hk₀, hr₀, hne₀⟩ := Nat.find_spec hex
  have hmin : ∀ (i j : ℕ), i + j < i₀ + j₀ → ∀ v : V,
      complexGLTwoMoment i j (B v : Langlands.GeneralLinear 2 ℂ → ℂ) = 0 := by
    intro i j hij v
    by_contra h
    have hr : ((i + j : ℕ) : ℝ) ≤ s :=
      le_trans (by exact_mod_cast hij.le) hr₀
    exact Nat.find_min hex (hk₀ ▸ hij) ⟨i, j, v, rfl, hr, h⟩
  have hconv : ((i₀ + j₀ : ℕ) : ℝ) < 2 * ((d 0).exponent.re - (d 1).exponent.re) := by
    rw [← hs]; linarith
  set ℓ' : V →ₗ[ℂ] ℂ := (complexGLTwoMomentLinear d i₀ j₀ hM hconv).comp B with hℓ'
  have hℓ'_apply : ∀ v, ℓ' v = complexGLTwoMoment i₀ j₀ (B v : Langlands.GeneralLinear 2 ℂ → ℂ) :=
    fun v => rfl
  refine ⟨ℓ',
    ![2 * (d 1).exponent + 1 + ((i₀ + j₀ : ℕ) : ℂ), 2 * (d 0).exponent - 1 - ((i₀ + j₀ : ℕ) : ℂ)],
    ![Complex.I * (((d 1).weight : ℂ) + (i₀ : ℂ) - (j₀ : ℂ)),
      Complex.I * (((d 0).weight : ℂ) - (i₀ : ℂ) + (j₀ : ℂ))], ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    apply hne₀
    rw [← hℓ'_apply, h, LinearMap.zero_apply]
  · intro X hX v
    rw [hℓ'_apply, hBemb.2 X v, (hM d i₀ j₀ hconv _ (B v).2).2.1 X hX]
    have h1 : (i₀ : ℂ) * complexGLTwoMoment (i₀ - 1) j₀
        (B v : Langlands.GeneralLinear 2 ℂ → ℂ) = 0 := by
      rcases Nat.eq_zero_or_pos i₀ with h | h
      · simp [h]
      · rw [hmin (i₀ - 1) j₀ (by omega) v, mul_zero]
    have h2 : (j₀ : ℂ) * complexGLTwoMoment i₀ (j₀ - 1)
        (B v : Langlands.GeneralLinear 2 ℂ → ℂ) = 0 := by
      rcases Nat.eq_zero_or_pos j₀ with h | h
      · simp [h]
      · rw [hmin i₀ (j₀ - 1) (by omega) v, mul_zero]
    linear_combination (-(X 0 1)) * h1 - starRingEnd ℂ (X 0 1) * h2
  · intro k v
    simp only [hℓ'_apply, hBemb.2 _ v]
    exact (hM d i₀ j₀ hconv _ (B v).2).2.2 k
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ha0, ha1]
    ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.natCast_re]
    norm_num
    have : ((i₀ + j₀ : ℕ) : ℝ) ≤ s := hr₀
    push_cast at this
    rw [hs] at this
    linarith

end Langlands.Archimedean
