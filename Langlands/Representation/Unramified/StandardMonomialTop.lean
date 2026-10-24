import Langlands.Representation.Unramified.StandardMonomialSupport

/-! # Nonvanishing of the top coefficient of standard Hecke monomials -/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure GeneralLinear.Iwasawa

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance topFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance topFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance topFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance topGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance topGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance topGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance topGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance topGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- A spherical Hecke function takes nonnegative real values. -/
def SphericalNonnegative {r : ℕ} (f : SphericalHeckeAlgebra F r) : Prop :=
  ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re

variable {F}

/-- Convolution preserves nonnegative real values. -/
theorem sphericalNonnegative_mul {r : ℕ} {f g : SphericalHeckeAlgebra F r}
    (hf : SphericalNonnegative F f) (hg : SphericalNonnegative F g) :
    SphericalNonnegative F (f * g) := by
  intro x
  have hi := Hecke.TestFunction.convolutionIntegrand_integrable (sphericalHaar F r)
    f.val g.val x
  constructor
  · have hm : ((f * g) x).im = ∫ y, (f y * g (y⁻¹ * x)).im ∂sphericalHaar F r :=
      (integral_im hi).symm
    rw [hm]
    simp only [Complex.mul_im, (hf _).1, (hg _).1,
      mul_zero, zero_mul, add_zero, integral_zero]
  · have hm : ((f * g) x).re = ∫ y, (f y * g (y⁻¹ * x)).re ∂sphericalHaar F r :=
      (integral_re hi).symm
    rw [hm]
    apply integral_nonneg
    intro y
    simp only [Complex.mul_re, (hf _).1, zero_mul, sub_zero]
    exact mul_nonneg (hf _).2 (hg _).2

/-- Convolution of nonnegative real functions is positive at a product of points
where the respective functions are positive. -/
theorem spherical_mul_re_pos {r : ℕ} {f g : SphericalHeckeAlgebra F r}
    (hf : SphericalNonnegative F f) (hg : SphericalNonnegative F g)
    {x y : GeneralLinear (r + 1) F.Carrier} (hx : 0 < (f x).re) (hy : 0 < (g y).re) :
    0 < ((f * g) (x * y)).re := by
  have hi := Hecke.TestFunction.convolutionIntegrand_integrable (sphericalHaar F r)
    f.val g.val (x * y)
  have hm : ((f * g) (x * y)).re =
      ∫ z, (f z * g (z⁻¹ * (x * y))).re ∂sphericalHaar F r := (integral_re hi).symm
  rw [hm]
  refine integral_pos_of_integrable_nonneg_nonzero
    (f := fun z => (f z * g (z⁻¹ * (x * y))).re) (x := x) ?_ hi.re ?_ ?_
  · have hfc : Continuous (fun z => f z) := f.val.continuous
    have hgc : Continuous (fun z => g z) := g.val.continuous
    exact Complex.continuous_re.comp
      (hfc.mul (hgc.comp (continuous_inv.mul continuous_const)))
  · intro z
    change 0 ≤ (f z * g (z⁻¹ * (x * y))).re
    simp only [Complex.mul_re, (hf _).1, zero_mul, sub_zero]
    exact mul_nonneg (hf _).2 (hg _).2
  · simp only [inv_mul_cancel_left, Complex.mul_re, (hf _).1, zero_mul, sub_zero]
    exact (mul_pos hx hy).ne'

/-- The standard double-coset indicators are nonnegative. -/
theorem sphericalNonnegative_standard {r : ℕ} (i : Fin (r + 2)) :
    SphericalNonnegative F (standardHeckeElement F r i) := by
  intro x
  rw [standardHeckeElement_apply]
  by_cases hx : x ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardDiagonal F r i)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- A standard Hecke element takes value one at its defining diagonal. -/
theorem standardHeckeElement_self {r : ℕ} (i : Fin (r + 2)) :
    standardHeckeElement F r i (standardDiagonal F r i) = 1 := by
  rw [standardHeckeElement_apply, Set.indicator_of_mem
    (Hecke.TestFunction.mem_doubleCosetSet_self _ _)]

/-- The unit of the spherical corner is nonnegative. -/
theorem sphericalNonnegative_one (r : ℕ) :
    SphericalNonnegative F (1 : SphericalHeckeAlgebra F r) := by
  simpa only [standardHeckeElement_zero] using
    (sphericalNonnegative_standard (F := F) (r := r) 0)

/-- The unit takes value one at the group identity. -/
theorem spherical_one_apply_one (r : ℕ) :
    (1 : SphericalHeckeAlgebra F r) (1 : GeneralLinear (r + 1) F.Carrier) = 1 := by
  simpa only [standardHeckeElement_zero, standardDiagonal_zero] using
    (standardHeckeElement_self (F := F) (r := r) 0)

/-- Nonnegative spherical functions remain nonnegative under natural powers. -/
theorem sphericalNonnegative_pow {r : ℕ} {f : SphericalHeckeAlgebra F r}
    (hf : SphericalNonnegative F f) (n : ℕ) : SphericalNonnegative F (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using sphericalNonnegative_one (F := F) r
  | succ n ih => simpa only [pow_succ] using sphericalNonnegative_mul ih hf

/-- Positivity at a point propagates to powers at the corresponding group powers. -/
theorem spherical_pow_re_pos {r : ℕ} {f : SphericalHeckeAlgebra F r}
    (hf : SphericalNonnegative F f) {x : GeneralLinear (r + 1) F.Carrier}
    (hx : 0 < (f x).re) (n : ℕ) : 0 < ((f ^ n) (x ^ n)).re := by
  induction n with
  | zero => simp only [pow_zero, spherical_one_apply_one, Complex.one_re]; exact zero_lt_one
  | succ n ih =>
    simpa only [pow_succ] using
      spherical_mul_re_pos (sphericalNonnegative_pow hf n) hf ih hx

/-- Addition of exponents multiplies the corresponding torus elements. -/
theorem standardTorus_add {r : ℕ} (a b : Fin (r + 1) → ℤ) :
    standardTorus F (a + b) = standardTorus F a * standardTorus F b := by
  unfold standardTorus torus
  rw [← map_mul]
  congr 1
  funext j
  exact zpow_add _ _ _

@[simp] theorem standardTorus_zero (r : ℕ) :
    standardTorus F (0 : Fin (r + 1) → ℤ) = 1 := by
  simp [standardTorus, torus]
  exact map_one diagonalUnits

/-- Powers of standard diagonal elements add their standard exponents. -/
theorem standardDiagonal_pow_eq_torus {r : ℕ} (i : Fin (r + 2)) (n : ℕ) :
    standardDiagonal F r i ^ n = standardTorus F (n • standardExponent i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', succ_nsmul', standardTorus_add, ih, standardDiagonal_eq_torus]

/-- A list product of powers of standard elements has nonnegative values and is
positive at the torus whose exponent is the sum of the factor exponents. -/
theorem standardMonomial_list_top {r : ℕ} (l : List (Fin (r + 2) × ℕ)) :
    SphericalNonnegative F (l.map fun q => standardHeckeElement F r q.1 ^ q.2).prod ∧
    0 < ((l.map fun q => standardHeckeElement F r q.1 ^ q.2).prod
      (standardTorus F (l.map fun q => q.2 • standardExponent q.1).sum)).re := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, standardTorus_zero,
      spherical_one_apply_one, Complex.one_re]
    exact ⟨sphericalNonnegative_one r, zero_lt_one⟩
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, standardTorus_add]
    have hq := sphericalNonnegative_pow (sphericalNonnegative_standard (F := F) q.1) q.2
    refine ⟨sphericalNonnegative_mul hq ih.1, ?_⟩
    apply spherical_mul_re_pos hq ih.1 _ ih.2
    rw [← standardDiagonal_pow_eq_torus]
    apply spherical_pow_re_pos (sphericalNonnegative_standard q.1)
    rw [standardHeckeElement_self, Complex.one_re]
    exact zero_lt_one

/-- The leading torus coefficient of each standard monomial is strictly positive. -/
theorem standardMonomial_top_re_pos {r : ℕ} (a : Fin (r + 2) → ℕ) :
    0 < (standardMonomial F a (standardTorus F (monomialExponent a))).re := by
  have h := (standardMonomial_list_top (F := F) (List.ofFn fun i => (i, a i))).2
  rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
  rw [monomialExponent_eq_sum]
  exact h

/-- The leading torus coefficient of each standard monomial is nonzero. -/
theorem standardMonomial_top_ne_zero {r : ℕ} (a : Fin (r + 2) → ℕ) :
    standardMonomial F a (standardTorus F (monomialExponent a)) ≠ 0 := by
  intro h
  have hp := standardMonomial_top_re_pos (F := F) a
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl _ hp)

/-- Dominance support and the nonzero leading coefficient give triangularity. -/
theorem standardMonomialTriangularity (F : PadicField.{uF} p) :
    StandardMonomialTriangularity F :=
  fun _ a => ⟨standardMonomial_support (F := F) a, standardMonomial_top_ne_zero (F := F) a⟩

end Langlands.Unramified
