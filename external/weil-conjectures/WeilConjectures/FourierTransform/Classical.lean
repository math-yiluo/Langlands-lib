/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Trace.Defs
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The classical Fourier transform on a finite affine space

Let `ψ` be an additive character of a field `K`, `L` a finite extension of `K` and `ι` a finite
index type, for instance `K = 𝔽_q`, `L = 𝔽_{qⁿ}` and `#ι = r`. The character
`ψ_L = ψ ∘ Tr_{L/K}` and the standard pairing `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` of `L^ι` define the classical
Fourier transform of functions `f : L^ι → R`,

`f̂(y) = ∑_{x ∈ L^ι} f(x) ψ(Tr_{L/K}⟨x, y⟩)`.

By the Fourier trace formula, it is the function-theoretic model of the Fourier–Deligne
transform: up to sign, the trace function of the Fourier–Deligne transform of a Weil complex on
the affine space `𝔸^ι` is the classical Fourier transform of its trace function. The two
numerical identities of the Fourier–Deligne transform, Plancherel and trace-level Fourier
inversion, are consequences of the corresponding identities for `f ↦ f̂` proved here, which in
turn follow from the orthogonality relations on `L^ι`, the product over `ι` of the orthogonality
relations `AddChar.sum_compTrace_sub_mul` on `L`.

For `ι` with one element, `L^ι = L` and the transform is the transform `f̂(y) = ∑ₓ f(x) ψ_L(x y)`
of functions on `L` (`FiniteField.fourierTransform`, `FiniteField.fourierTransformPi_unique`);
its inversion and Plancherel identities are the case `ι = Unit` of those on `L^ι`.

## Main declarations

- `FiniteField.fourierTransformPi`: the classical Fourier transform `f ↦ f̂` on `L^ι` with
  respect to `ψ ∘ Tr_{L/K}`.
- `FiniteField.fourierTransform`: the classical Fourier transform of functions on `L`.

## Main statements

- `FiniteField.sum_compTrace_sum_sub_mul`: orthogonality of the characters
  `y ↦ ψ(Tr⟨x, y⟩)` of `L^ι`.
- `FiniteField.fourierTransformPi_inv_fourierTransformPi`: classical Fourier inversion,
  `(f̂)^∨ = #L ^ #ι · f`, the second transform taken with respect to `ψ⁻¹`, and
  `FiniteField.fourierTransform_inv_fourierTransform`, its case `ι = Unit`.
- `FiniteField.sum_norm_sq_fourierTransformPi`: the classical Plancherel identity
  `∑_y |j f̂(y)|² = #L ^ #ι ∑_x |j f(x)|²` for an embedding `j` of the values into `ℂ`, and
  `FiniteField.sum_norm_sq_fourierTransform`, its case `ι = Unit`.
-/

@[expose] public section

open ComplexConjugate

namespace FiniteField

variable {K L R ι : Type*} [Field K] [Field L] [Fintype L] [Algebra K L] [CommRing R]
  [Fintype ι] [DecidableEq ι]

/-- The *classical Fourier transform* `f̂(y) = ∑ₓ f(x) ψ(Tr_{L/K}⟨x, y⟩)` of a function
`f : L^ι → R` on a finite affine space, `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` being the standard pairing, with
respect to the additive character `ψ ∘ Tr_{L/K}` of `L` induced by an additive character `ψ` of a
subfield `K`. -/
noncomputable def fourierTransformPi (ψ : AddChar K R) (f : (ι → L) → R) (y : ι → L) : R :=
  ∑ x, f x * ψ (Algebra.trace K L (∑ i, x i * y i))

lemma fourierTransformPi_eq_sum_compTrace (ψ : AddChar K R) (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ f y = ∑ x, f x * ψ.compTrace L (∑ i, x i * y i) :=
  rfl

/-- The classical Fourier transform on `L^ι` commutes with negation. -/
lemma fourierTransformPi_neg (ψ : AddChar K R) (f : (ι → L) → R) :
    fourierTransformPi ψ (fun x ↦ -f x) = fun y ↦ -fourierTransformPi ψ f y := by
  ext y
  simp [fourierTransformPi]

/-- The classical Fourier transform on `L^ι` is linear over the constants. -/
lemma fourierTransformPi_const_mul (ψ : AddChar K R) (c : R) (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ (fun x ↦ c * f x) y = c * fourierTransformPi ψ f y := by
  simp [fourierTransformPi, Finset.mul_sum, mul_assoc]

/-- The *classical Fourier transform* `f̂(y) = ∑ₓ f(x) ψ(Tr_{L/K}(x y))` of a function
`f : L → R` on a finite field `L`, with respect to the additive character `ψ ∘ Tr_{L/K}` of `L`
induced by an additive character `ψ` of a subfield `K`. For `L = 𝔽_{qⁿ}` over `K = 𝔽_q` this
is the transform with respect to the character `ψₙ` of `𝔽_{qⁿ}`. It is the transform on `L^ι`
for `ι` with one element (`FiniteField.fourierTransformPi_unique`).
(sketch blueprint: `definition-trace-function`) -/
noncomputable def fourierTransform (ψ : AddChar K R) (f : L → R) (y : L) : R :=
  ∑ x, f x * ψ (Algebra.trace K L (x * y))

lemma fourierTransform_eq_sum_compTrace (ψ : AddChar K R) (f : L → R) (y : L) :
    fourierTransform ψ f y = ∑ x, f x * ψ.compTrace L (x * y) :=
  rfl

/-- The classical Fourier transform is additive in the function; in particular it commutes with
negation. -/
lemma fourierTransform_neg (ψ : AddChar K R) (f : L → R) :
    fourierTransform ψ (fun x ↦ -f x) = fun y ↦ -fourierTransform ψ f y := by
  ext y
  simp [fourierTransform, Finset.sum_neg_distrib]

omit [Field L] [Fintype ι] [DecidableEq ι] in
/-- A sum over the vectors `L^ι`, for `ι` with one element, is a sum over `L`. -/
lemma sum_funUnique [Unique ι] [Fintype (ι → L)] {M : Type*} [AddCommMonoid M]
    (g : (ι → L) → M) : ∑ x, g x = ∑ a, g fun _ ↦ a :=
  Fintype.sum_equiv (Equiv.funUnique ι L) _ _ fun x ↦
    congrArg g (funext fun i ↦ congrArg x (Unique.uniq _ i))

/-- For `ι` with one element, the classical Fourier transform on `L^ι = L` is the classical
Fourier transform on `L`: a one-term pairing is the product. -/
lemma fourierTransformPi_unique [Unique ι] (ψ : AddChar K R) (f : (ι → L) → R) (y : L) :
    fourierTransformPi ψ f (fun _ ↦ y) = fourierTransform ψ (fun x ↦ f fun _ ↦ x) y := by
  rw [fourierTransformPi, sum_funUnique]
  simp only [Fintype.sum_unique]
  rfl

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDomain R]

/-- **Additive orthogonality on `L^ι`.** For a nontrivial additive character `ψ` of `K`,
`∑_{y ∈ L^ι} ψ_L(⟨x - x', y⟩) = #L ^ #ι` if `x = x'` and `0` otherwise: the sum is the product
over `ι` of the orthogonality relations on `L`.
(blueprint: `corollary-plancherel--1`; sketch blueprint: `corollary-plancherel--1`) -/
theorem sum_compTrace_sum_sub_mul [DecidableEq L] {ψ : AddChar K R} (hψ : ψ ≠ 1) (x x' : ι → L) :
    ∑ y : ι → L, ψ.compTrace L (∑ i, (x i - x' i) * y i) =
      if x = x' then (Fintype.card L : R) ^ Fintype.card ι else 0 := by
  classical
  have hprod (t : ι → L) : ψ.compTrace L (∑ i, t i) = ∏ i, ψ.compTrace L (t i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun i (t : L) ↦ ψ.compTrace L ((x i - x' i) * t))]
  simp_rw [AddChar.sum_compTrace_sub_mul hψ]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- **Classical Fourier inversion on `L^ι`.** For a nontrivial additive character `ψ` of `K`,
the transform with respect to `ψ⁻¹` of the transform with respect to `ψ` is `#L ^ #ι` times
the identity. (sketch blueprint: `det-prop-double-trace`, proof) -/
theorem fourierTransformPi_inv_fourierTransformPi {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : (ι → L) → R) (y : ι → L) :
    fourierTransformPi ψ⁻¹ (fourierTransformPi ψ f) y =
      (Fintype.card L : R) ^ Fintype.card ι * f y := by
  classical
  have h (z : ι → L) : ∑ x : ι → L, f z * ψ.compTrace L (∑ i, z i * x i) *
      ψ⁻¹.compTrace L (∑ i, x i * y i) =
      f z * ∑ x : ι → L, ψ.compTrace L (∑ i, (z i - y i) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_assoc, AddChar.compTrace_apply, AddChar.compTrace_apply, AddChar.inv_apply,
      ← AddChar.map_add_eq_mul, ← map_neg, ← map_add, AddChar.compTrace_apply]
    congr 3
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [fourierTransformPi_eq_sum_compTrace, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [h, sum_compTrace_sum_sub_mul hψ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ y, ite_eq_left (Finset.mem_univ _), mul_comm]

/-- **Classical Fourier inversion.** For a nontrivial additive character `ψ` of `K`, the
transform with respect to `ψ⁻¹` of the transform with respect to `ψ` is `#L` times the
identity: `∑_x (∑_z f(z) ψ_L(z x)) ψ_L(-x y) = #L · f(y)`. It is the case `ι = Unit` of
`FiniteField.fourierTransformPi_inv_fourierTransformPi`.
(sketch blueprint: `det-prop-double-trace`, proof) -/
theorem fourierTransform_inv_fourierTransform {ψ : AddChar K R} (hψ : ψ ≠ 1) (f : L → R)
    (y : L) :
    fourierTransform ψ⁻¹ (fourierTransform ψ f) y = Fintype.card L * f y := by
  have h := fourierTransformPi_inv_fourierTransformPi (ι := Unit) hψ (fun x ↦ f (x ())) fun _ ↦ y
  simp only [fourierTransformPi_unique, Fintype.card_unit, pow_one] at h
  exact h

omit [Fintype L] [Algebra.IsSeparable K L] [IsDomain R] in
/-- The values of an additive character of a finite field, embedded in `ℂ`, are roots of
unity, so complex conjugation inverts them. -/
lemma conj_ringHom_compTrace [Finite K] (j : R →+* ℂ) (ψ : AddChar K R) (t : L) :
    conj (j (ψ.compTrace L t)) = j (ψ.compTrace L (-t)) := by
  have : Finite L := Module.finite_of_finite K
  let := Fintype.ofFinite L
  have hpow : j (ψ.compTrace L t) ^ Fintype.card L = 1 := by
    rw [← map_pow, ← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one,
      map_one]
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero
  rw [← Complex.inv_eq_conj hnorm]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← map_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, map_one]

/-- **Classical Plancherel identity on `L^ι`.** For a nontrivial additive character `ψ` of a
finite field `K`, a finite extension `L / K` and a ring homomorphism `j : R →+* ℂ`,
`∑_y |j f̂(y)|² = #L ^ #ι ∑_x |j f(x)|²`.
(sketch blueprint: `corollary-plancherel`, proof) -/
theorem sum_norm_sq_fourierTransformPi [Finite K] (j : R →+* ℂ) {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : (ι → L) → R) :
    ∑ y, ‖j (fourierTransformPi ψ f y)‖ ^ 2 =
      (Fintype.card L : ℝ) ^ Fintype.card ι * ∑ x, ‖j (f x)‖ ^ 2 := by
  classical
  set g : (ι → L) → ℂ := fun x ↦ j (f x)
  set e : L → ℂ := fun t ↦ j (ψ.compTrace L t)
  have hf (y : ι → L) : j (fourierTransformPi ψ f y) = ∑ x, g x * e (∑ i, x i * y i) := by
    simp [fourierTransformPi_eq_sum_compTrace, g, e]
  have horth (x x' : ι → L) : ∑ y : ι → L, e (∑ i, (x i - x' i) * y i) =
      if x = x' then (Fintype.card L : ℂ) ^ Fintype.card ι else 0 := by
    simp only [e]
    rw [← map_sum, sum_compTrace_sum_sub_mul hψ]
    split_ifs <;> simp
  have hy (y : ι → L) : j (fourierTransformPi ψ f y) * conj (j (fourierTransformPi ψ f y)) =
      ∑ x, ∑ x', g x * conj (g x') * e (∑ i, (x i - x' i) * y i) := by
    rw [hf, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun x' _ ↦ ?_
    simp only [e]
    rw [map_mul (starRingEnd ℂ), conj_ringHom_compTrace,
      show ∑ i, (x i - x' i) * y i = ∑ i, x i * y i + -∑ i, x' i * y i by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring,
      AddChar.map_add_eq_mul, map_mul j]
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
    ← Complex.mul_conj', hy]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm).trans ?_
  simp_rw [← Finset.mul_sum, horth, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- **Classical Plancherel identity.** For a nontrivial additive character `ψ` of a finite field
`K`, a finite extension `L / K` and a ring homomorphism `ι : R →+* ℂ`,
`∑_y |ι f̂(y)|² = #L ∑_x |ι f(x)|²`. It is the case `ι = Unit` of
`FiniteField.sum_norm_sq_fourierTransformPi`.
(sketch blueprint: `corollary-plancherel`, proof) -/
theorem sum_norm_sq_fourierTransform [Finite K] (ι : R →+* ℂ) {ψ : AddChar K R} (hψ : ψ ≠ 1)
    (f : L → R) :
    ∑ y, ‖ι (fourierTransform ψ f y)‖ ^ 2 = Fintype.card L * ∑ x, ‖ι (f x)‖ ^ 2 := by
  have h := sum_norm_sq_fourierTransformPi (ι := Unit) ι hψ fun x ↦ f (x ())
  rw [sum_funUnique, sum_funUnique, Fintype.card_unit, pow_one] at h
  simp only [fourierTransformPi_unique] at h
  exact h

end FiniteField
