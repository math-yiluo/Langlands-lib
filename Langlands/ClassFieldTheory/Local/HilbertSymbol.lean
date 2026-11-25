import Langlands.ClassFieldTheory.Local.QuadraticNormBall
import Langlands.Group.Unitary.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension

/-!
# The quadratic Hilbert symbol of a nonarchimedean local field

GKT Appendix B.3, Proposition B.51 (iv), (v) and Corollary B.52 (b) (p. 625): for a nonarchimedean
local field `F` with `2 ≠ 0` and `a, b ∈ Fˣ`, the quadratic Hilbert symbol `(a, b)_F ∈ {±1}` is `1`
exactly when `a` is a square or `b` is a norm from `F(√a)`, equivalently when the conic
`a x² + b y² = z²` has a non-trivial point.

`hilbertSymbol a : Fˣ →* ℤˣ` is `1` if `a` is a square, and otherwise the quadratic character
`LocalClassField.normResidueSign F F(√a)` of the extension `F(√a) = QuadraticAlgebra F a 0`
(`1` on the norms, `-1` elsewhere; a character because the norms have index two, by local class
field theory). Then:

* `hilbertSymbol_eq_one_iff`: `(a, b) = 1 ↔ ∃ x y, x² - a y² = b`;
  `hilbertSymbol_eq_one_iff_exists_conic`: `↔` the conic `z² = a x² + b y²` has a non-trivial point;
* `hilbertSymbol_comm` (symmetry), `hilbertSymbol_mul_left`, `map_mul` (bimultiplicativity);
* `hilbertSymbol_neg_self` (`(a, -a) = 1`), `hilbertSymbol_one_sub` (`(a, 1 - a) = 1`),
  `hilbertSymbol_self` (`(a, a) = (a, -1)`), `hilbertSymbol_sq_right` (`(a, c²) = 1`);
* `exists_hilbertSymbol_eq_neg_one`: non-degeneracy, `(a, ·)` is non-trivial for a non-square `a`;
* `normResidueSign_eq_hilbertSymbol`: for any quadratic extension `E = F(δ)` with `δ² = d`,
  `η_{E/F} = (d, ·)_F`.
-/

noncomputable section

namespace Langlands.LocalClassField

open QuadraticAlgebra

/-! ### The quadratic algebra `F(√a)` and its conjugation -/

section QuadraticAlgebra

variable {F : Type*} [Field F]

/-- The conjugation `x + y ω ↦ x - y ω` of `F[ω] = QuadraticAlgebra F a 0`, `ω² = a`. -/
def quadraticAlgebraConj (a : F) : QuadraticAlgebra F a 0 →ₐ[F] QuadraticAlgebra F a 0 :=
  QuadraticAlgebra.lift ⟨-ω, by rw [neg_mul_neg, omega_mul_omega_eq_add]; simp⟩

theorem quadraticAlgebraConj_apply (a : F) (z : QuadraticAlgebra F a 0) :
    quadraticAlgebraConj a z = ⟨z.re, -z.im⟩ := by
  ext <;> simp [quadraticAlgebraConj, QuadraticAlgebra.lift]

/-- `F[ω]`, `ω² = a ≠ 0`, with its conjugation is a quadratic involution. -/
theorem isQuadraticInvolution_quadraticAlgebraConj {a : F} (ha : a ≠ 0) :
    IsQuadraticInvolution (quadraticAlgebraConj a) (ω : QuadraticAlgebra F a 0) where
  isUnit := by
    refine IsUnit.of_mul_eq_one (a⁻¹ • ω) ?_
    rw [mul_smul_comm, omega_mul_omega_eq_add]
    ext <;> simp [ha]
  map_eq_neg := by rw [quadraticAlgebraConj_apply]; ext <;> simp
  exists_basis := ⟨QuadraticAlgebra.basis a 0, by rw [QuadraticAlgebra.basis_apply_zero],
    by rw [QuadraticAlgebra.basis_apply_one]⟩

/-- The norm of `F[ω]` is `x² - a y²`. -/
theorem algebra_norm_quadraticAlgebra (a : F) (z : QuadraticAlgebra F a 0) :
    Algebra.norm F z = z.re ^ 2 - a * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  erw [det_toLinearMap_eq_norm z]
  rw [norm_def]
  ring

end QuadraticAlgebra

/-! ### The Hilbert symbol -/

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [NeZero (2 : F)]

variable (F) in
open Classical in
/-- **The quadratic Hilbert symbol** `(a, b)_F` of a nonarchimedean local field with `2 ≠ 0`
(GKT Proposition B.51 (v), Corollary B.52 (b)): `1` if `a` is a square, and otherwise the
quadratic character of `F(√a) / F`, `1` on the norms from `F(√a)` and `-1` elsewhere. A homomorphism
in `b`; it is symmetric (`hilbertSymbol_comm`). -/
def hilbertSymbol (a : Fˣ) : Fˣ →* ℤˣ :=
  if h : IsSquare (a : F) then 1 else
    haveI : Fact (¬ IsSquare (a : F)) := ⟨h⟩
    haveI := (isQuadraticInvolution_quadraticAlgebraConj a.ne_zero).isGalois
    normResidueSign F (QuadraticAlgebra F (a : F) 0)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a square `a`, every `b` is `x² - a y²` (the hyperbolic plane represents everything). -/
theorem exists_sq_sub_mul_sq_of_isSquare {a : F} (ha : a ≠ 0) (h : IsSquare a) (b : F) :
    ∃ x y : F, x ^ 2 - a * y ^ 2 = b := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by rintro rfl; simp at ha
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨(1 + b) / 2, (b - 1) / (2 * r), ?_⟩
  field_simp
  ring

/-- **`(a, b)_F = 1` if and only if `b` is represented by `x² - a y²`** (GKT Proposition B.51 (v):
`a` is a square or `b` is a norm from `F(√a)`). -/
theorem hilbertSymbol_eq_one_iff (a b : Fˣ) :
    hilbertSymbol F a b = 1 ↔ ∃ x y : F, x ^ 2 - a * y ^ 2 = b := by
  classical
  by_cases h : IsSquare (a : F)
  · simp only [hilbertSymbol, h, dite_true, MonoidHom.one_apply, true_iff]
    exact exists_sq_sub_mul_sq_of_isSquare a.ne_zero h b
  · have : Fact (¬ IsSquare (a : F)) := ⟨h⟩
    have := (isQuadraticInvolution_quadraticAlgebraConj a.ne_zero).isGalois
    simp only [hilbertSymbol, h, dite_false]
    rw [normResidueSign_eq_one_iff]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(z : QuadraticAlgebra F (a : F) 0).re, (z : QuadraticAlgebra F (a : F) 0).im, ?_⟩
      have := congrArg Units.val hz
      rw [Units.coe_map, algebra_norm_quadraticAlgebra] at this
      exact this
    · rintro ⟨x, y, hxy⟩
      have hz : (⟨x, y⟩ : QuadraticAlgebra F (a : F) 0) ≠ 0 := by
        intro h0
        have hx : x = 0 := congrArg QuadraticAlgebra.re h0
        have hy : y = 0 := congrArg QuadraticAlgebra.im h0
        subst hx hy
        exact b.ne_zero (by rw [← hxy]; ring)
      refine ⟨Units.mk0 _ hz, Units.ext ?_⟩
      rw [Units.coe_map, Units.val_mk0, algebra_norm_quadraticAlgebra]
      exact hxy

theorem hilbertSymbol_eq_one_or (a b : Fˣ) :
    hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 :=
  Int.units_eq_one_or _

theorem hilbertSymbol_mul_self (a b : Fˣ) : hilbertSymbol F a b * hilbertSymbol F a b = 1 := by
  rcases hilbertSymbol_eq_one_or a b with h | h <;> rw [h] <;> decide

theorem hilbertSymbol_eq_neg_one_iff (a b : Fˣ) :
    hilbertSymbol F a b = -1 ↔ ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b := by
  rw [← hilbertSymbol_eq_one_iff]
  rcases hilbertSymbol_eq_one_or a b with h | h <;> simp [h]

/-- **The conic criterion** (GKT Proposition B.51 (iv)): `(a, b)_F = 1` if and only if
`z² = a x² + b y²` has a solution `(x, y, z) ≠ 0`. -/
theorem hilbertSymbol_eq_one_iff_exists_conic (a b : Fˣ) :
    hilbertSymbol F a b = 1 ↔
      ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  rw [hilbertSymbol_eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨y, 1, x, Or.inr (Or.inl one_ne_zero), by rw [← h]; ring⟩
  · rintro ⟨x, y, z, hne, h⟩
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by
        rintro rfl
        rcases hne with h' | h' | h'
        · exact h' rfl
        · exact h' rfl
        · exact h' (pow_eq_zero_iff two_ne_zero |>.1 (by rw [h]; ring))
      refine exists_sq_sub_mul_sq_of_isSquare a.ne_zero ⟨z / x, ?_⟩ b
      field_simp
      linear_combination -h
    · refine ⟨z / y, x / y, ?_⟩
      field_simp
      linear_combination h

/-- **The Hilbert symbol is symmetric.** -/
theorem hilbertSymbol_comm (a b : Fˣ) : hilbertSymbol F a b = hilbertSymbol F b a := by
  have key : hilbertSymbol F a b = 1 ↔ hilbertSymbol F b a = 1 := by
    rw [hilbertSymbol_eq_one_iff_exists_conic, hilbertSymbol_eq_one_iff_exists_conic]
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      exact ⟨y, x, z, by tauto, by rw [h]; ring⟩
    · rintro ⟨x, y, z, hne, h⟩
      exact ⟨y, x, z, by tauto, by rw [h]; ring⟩
  rcases hilbertSymbol_eq_one_or a b with h | h <;>
    rcases hilbertSymbol_eq_one_or b a with h' | h'
  · rw [h, h']
  · exact absurd (key.1 h) (by rw [h']; decide)
  · exact absurd (key.2 h') (by rw [h]; decide)
  · rw [h, h']

/-- **The Hilbert symbol is multiplicative in the first variable** (with `map_mul` in the second,
bimultiplicative). -/
theorem hilbertSymbol_mul_left (a a' b : Fˣ) :
    hilbertSymbol F (a * a') b = hilbertSymbol F a b * hilbertSymbol F a' b := by
  rw [hilbertSymbol_comm, map_mul, hilbertSymbol_comm b a, hilbertSymbol_comm b a']

/-- `(∏ aᵢ, b)_F = ∏ (aᵢ, b)_F`. -/
theorem hilbertSymbol_prod_left {ι : Type*} (s : Finset ι) (a : ι → Fˣ) (b : Fˣ) :
    hilbertSymbol F (∏ i ∈ s, a i) b = ∏ i ∈ s, hilbertSymbol F (a i) b := by
  rw [hilbertSymbol_comm, map_prod]
  exact Finset.prod_congr rfl fun i _ => hilbertSymbol_comm _ _

theorem hilbertSymbol_one_left (b : Fˣ) : hilbertSymbol F 1 b = 1 :=
  (hilbertSymbol_eq_one_iff 1 b).2 (exists_sq_sub_mul_sq_of_isSquare (a := ((1 : Fˣ) : F))
    (by simp) ⟨1, by simp⟩ (b : F))

/-- `(a, c²) = 1`. -/
theorem hilbertSymbol_sq_right (a c : Fˣ) : hilbertSymbol F a (c ^ 2) = 1 :=
  (hilbertSymbol_eq_one_iff a _).2 ⟨c, 0, by simp⟩

/-- `(c², b) = 1`. -/
theorem hilbertSymbol_sq_left (c b : Fˣ) : hilbertSymbol F (c ^ 2) b = 1 := by
  rw [hilbertSymbol_comm, hilbertSymbol_sq_right]

/-- `(a, b c²) = (a, b)`. -/
theorem hilbertSymbol_mul_sq_right (a b c : Fˣ) :
    hilbertSymbol F a (b * c ^ 2) = hilbertSymbol F a b := by
  rw [map_mul, hilbertSymbol_sq_right, mul_one]

/-- `(a c², b) = (a, b)`. -/
theorem hilbertSymbol_mul_sq_left (a b c : Fˣ) :
    hilbertSymbol F (a * c ^ 2) b = hilbertSymbol F a b := by
  rw [hilbertSymbol_mul_left, hilbertSymbol_sq_left, mul_one]

/-- `(a⁻¹, b) = (a, b)`. -/
theorem hilbertSymbol_inv_left (a b : Fˣ) : hilbertSymbol F a⁻¹ b = hilbertSymbol F a b := by
  have h := hilbertSymbol_mul_left (F := F) a⁻¹ a b
  rw [inv_mul_cancel, hilbertSymbol_one_left] at h
  calc hilbertSymbol F a⁻¹ b
        = hilbertSymbol F a⁻¹ b * (hilbertSymbol F a b * hilbertSymbol F a b) := by
          rw [hilbertSymbol_mul_self, mul_one]
    _ = (hilbertSymbol F a⁻¹ b * hilbertSymbol F a b) * hilbertSymbol F a b := by rw [mul_assoc]
    _ = hilbertSymbol F a b := by rw [← h, one_mul]

/-- `(a, b⁻¹) = (a, b)`. -/
theorem hilbertSymbol_inv_right (a b : Fˣ) : hilbertSymbol F a b⁻¹ = hilbertSymbol F a b := by
  rw [hilbertSymbol_comm, hilbertSymbol_inv_left, hilbertSymbol_comm]

/-- `(a, -a) = 1`. -/
theorem hilbertSymbol_neg_self (a : Fˣ) : hilbertSymbol F a (-a) = 1 :=
  (hilbertSymbol_eq_one_iff a _).2 ⟨0, 1, by simp⟩

/-- `(a, 1 - a) = 1` for `a ≠ 1`. -/
theorem hilbertSymbol_one_sub (a : Fˣ) (ha : (a : F) ≠ 1) :
    hilbertSymbol F a (Units.mk0 (1 - (a : F)) (sub_ne_zero.2 (Ne.symm ha))) = 1 :=
  (hilbertSymbol_eq_one_iff a _).2 ⟨1, 1, by simp⟩

/-- `(a, a) = (a, -1)`. -/
theorem hilbertSymbol_self (a : Fˣ) : hilbertSymbol F a a = hilbertSymbol F a (-1) := by
  have h := hilbertSymbol_neg_self (F := F) a
  rw [← neg_one_mul, map_mul] at h
  calc hilbertSymbol F a a = (hilbertSymbol F a (-1) * hilbertSymbol F a a) * hilbertSymbol F a a :=
        by rw [h, one_mul]
    _ = hilbertSymbol F a (-1) * (hilbertSymbol F a a * hilbertSymbol F a a) := by rw [mul_assoc]
    _ = hilbertSymbol F a (-1) := by rw [hilbertSymbol_mul_self, mul_one]

/-- **Non-degeneracy**: for a non-square `a` there is `b` with `(a, b)_F = -1` (the norms from
`F(√a)` have index two). -/
theorem exists_hilbertSymbol_eq_neg_one {a : Fˣ} (h : ¬ IsSquare (a : F)) :
    ∃ b : Fˣ, hilbertSymbol F a b = -1 := by
  classical
  have : Fact (¬ IsSquare (a : F)) := ⟨h⟩
  have hG := (isQuadraticInvolution_quadraticAlgebraConj a.ne_zero).isGalois
  have hidx := index_range_norm_eq_two (F := F) (E := QuadraticAlgebra F (a : F) 0)
    (Algebra.IsQuadraticExtension.finrank_eq_two F _)
  by_contra hb
  push Not at hb
  have htop : (Units.map (Algebra.norm F : QuadraticAlgebra F (a : F) 0 →* F)).range = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    have h1 := hb b
    have h2 : hilbertSymbol F a b = 1 := (hilbertSymbol_eq_one_or a b).resolve_right h1
    simp only [hilbertSymbol, h, dite_false] at h2
    exact (normResidueSign_eq_one_iff).1 h2
  rw [htop, Subgroup.index_top] at hidx
  exact absurd hidx (by norm_num)

/-! ### Any quadratic extension -/

/-- **The quadratic character of a quadratic extension is a Hilbert symbol**: for `E = F(δ)` with
a quadratic involution `c` (`c δ = -δ`) and `δ² = d`, `η_{E/F}(t) = (d, t)_F`. -/
theorem normResidueSign_eq_hilbertSymbol {E : Type} [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsGalois F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) {d : Fˣ} (hd : δ * δ = algebraMap F E d) (t : Fˣ) :
    normResidueSign F E t = hilbertSymbol F d t := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have key : normResidueSign F E t = 1 ↔ hilbertSymbol F d t = 1 := by
    rw [normResidueSign_eq_one_iff, hilbertSymbol_eq_one_iff]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨x, y, hxy⟩ := hE.exists_eq (z : E)
      refine ⟨x, y, hE.algebraMap_injective ?_⟩
      have h1 := hE.algebraMap_norm (z : E)
      have h2 : Algebra.norm F (z : E) = t := by
        have := congrArg Units.val hz
        rwa [Units.coe_map] at this
      rw [h2] at h1
      rw [h1, hxy, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hE.map_eq_neg, map_sub,
        map_mul, map_pow, map_pow, ← hd]
      ring
    · rintro ⟨x, y, hxy⟩
      have hz : algebraMap F E x + algebraMap F E y * δ ≠ 0 := by
        intro h0
        have h3 : (algebraMap F E x + algebraMap F E y * δ) *
            c (algebraMap F E x + algebraMap F E y * δ) = algebraMap F E (t : F) := by
          rw [← hxy, map_sub, map_mul, map_pow, map_pow, ← hd, map_add, map_mul, AlgHom.commutes,
            AlgHom.commutes, hE.map_eq_neg]
          ring
        rw [h0, zero_mul] at h3
        exact t.ne_zero (hE.algebraMap_injective (by rw [← h3, map_zero]))
      refine ⟨Units.mk0 _ hz, Units.ext ?_⟩
      rw [Units.coe_map, Units.val_mk0]
      apply hE.algebraMap_injective
      rw [hE.algebraMap_norm, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hE.map_eq_neg,
        ← hxy, map_sub, map_mul, map_pow, map_pow, ← hd]
      ring
  rcases Int.units_eq_one_or (normResidueSign F E t) with h | h <;>
    rcases hilbertSymbol_eq_one_or d t with h' | h'
  · rw [h, h']
  · exact absurd (key.1 h) (by rw [h']; decide)
  · exact absurd (key.2 h') (by rw [h]; decide)
  · rw [h, h']

/-- The complex value `normSign E` of the quadratic character of `E = F(δ)`, `δ² = d`, is the
Hilbert symbol `(d, ·)_F`. -/
theorem normSign_eq_hilbertSymbol {E : Type} [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsGalois F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) {d : Fˣ} (hd : δ * δ = algebraMap F E d) (t : Fˣ) :
    normSign E t = ((hilbertSymbol F d t : ℤ) : ℂ) := by
  rw [normSign_eq_normResidueSign, normResidueSign_eq_hilbertSymbol hE hd]

end Langlands.LocalClassField
