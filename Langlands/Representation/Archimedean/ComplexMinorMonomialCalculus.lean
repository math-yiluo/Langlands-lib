import Langlands.Representation.Archimedean.ComplexLowestKTypeMultOne
import Langlands.Representation.Archimedean.ComplexLevelSpan
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration
import Langlands.Representation.Archimedean.ComplexPermutationKMap

/-!
# Minor monomials on `GL_n(ℂ)`: equivariance, smoothness, right derivatives, `U(n)`-finiteness

For `c : Fin n → ℕ` and `d : ℤ`, `ComplexLowestKType.minorMonomial c d g = det(g)^d ∏_j Δ_{j+1}(g)^{c_j}`
with `Δ_{j+1}` the minor on the bottom `j + 1` rows and the first `j + 1` columns. This file
proves the facts about `v = minorMonomial c d` on `GL_n(ℂ)` used by the product lemma
`ComplexMinorProductCyclic`:

* `minorMonomial_upper_mul`: `v(b g) = ∏_i b_ii^{l_i} · v(g)` for upper triangular `b` with
  nonzero diagonal, with `l_i = minorWeight c d i = d + ∑_{j : n-(j+1) ≤ i} c_j`;
* `minorMonomial_mul_upper`: `v(g y) = v(g) · rightChar c d y` for upper triangular `y`;
* `contMDiff_minorFun`: `v` is smooth on `GL_n(ℂ)`;
* `rightDerivative_minorFun`: for upper triangular `X`, `R(X) v = c_X · v` with the
  scalar `c_X = (d/dt) rightChar c d (1 + tX) |_{t=0}`;
* `minorFun_mem_kFiniteVectors`: `v` is `U(n)`-finite for right translation, and
  `mul_mem_kFiniteVectors`: products of `U(n)`-finite functions are `U(n)`-finite;
* `minorMonomial_revUnitary_ne_zero`: `v` does not vanish at the unitary antidiagonal
  permutation matrix `revUnitary n`.
-/

noncomputable section

open Matrix Finset
open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

set_option autoImplicit false

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

namespace ComplexMinorProduct

open ComplexLowestKType

variable {n : ℕ}

/-! ## Minors of products with triangular matrices -/

/-- A submatrix of a product factors through an injective intermediate index map `s` when the
terms of the matrix product outside the range of `s` vanish. -/
theorem submatrix_mul_of_vanish {m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (r c s : Fin m → Fin n) (hs : Function.Injective s)
    (h : ∀ i j (p : Fin n), p ∉ Set.range s → A (r i) p * B p (c j) = 0) :
    (A * B).submatrix r c = A.submatrix r s * B.submatrix s c := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_of_injective s hs _ _ (fun p hp => h i j p hp) (fun t => rfl)).symm

theorem topIdx_strictMono (j : Fin n) : StrictMono (topIdx j) := fun a b h => by
  rw [Fin.lt_def] at h ⊢
  simpa [topIdx] using h

/-- `Δ_{j+1}(b g) = (∏ of the bottom `j + 1` diagonal entries of `b`) · Δ_{j+1}(g)` for upper
triangular `b`: the bottom rows of `b g` only involve the bottom rows of `g`. -/
theorem minor_upper_mul (j : Fin n) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    minor j (b * g) = (∏ t, b (botIdx j t) (botIdx j t)) * minor j g := by
  unfold minor
  rw [submatrix_mul_of_vanish b g (botIdx j) (topIdx j) (botIdx j)
    (botIdx_strictMono j).injective, det_mul]
  · congr 1
    apply det_of_isUpperTriangular
    intro t t' htt'
    exact hb (botIdx_strictMono j htt')
  · intro t s p hp
    have hlt : p < botIdx j t := by
      by_contra hle
      push Not at hle
      apply hp
      have hp' : n - (j + 1) ≤ (p : ℕ) := by
        have := Fin.le_def.mp hle
        simp only [botIdx] at this
        omega
      refine ⟨⟨(p : ℕ) - (n - (j + 1)), by have := p.isLt; have := j.isLt; omega⟩, ?_⟩
      ext
      simp only [botIdx]
      omega
    have h0 : b (botIdx j t) p = 0 := hb hlt
    simp [h0]

/-- `Δ_{j+1}(g y) = Δ_{j+1}(g) · (∏ of the first `j + 1` diagonal entries of `y`)` for upper
triangular `y`: the first columns of `g y` only involve the first columns of `g`. -/
theorem minor_mul_upper (j : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) {y : Matrix (Fin n) (Fin n) ℂ}
    (hy : y.IsUpperTriangular) :
    minor j (g * y) = minor j g * ∏ t, y (topIdx j t) (topIdx j t) := by
  unfold minor
  rw [submatrix_mul_of_vanish g y (botIdx j) (topIdx j) (topIdx j)
    (topIdx_strictMono j).injective, det_mul]
  · congr 1
    apply det_of_isUpperTriangular
    intro t t' htt'
    exact hy (topIdx_strictMono j htt')
  · intro t s p hp
    have hlt : topIdx j s < p := by
      by_contra hle
      push Not at hle
      apply hp
      refine ⟨⟨(p : ℕ), ?_⟩, ?_⟩
      · have h1 : (p : ℕ) ≤ s := Fin.le_def.mp hle
        have := s.isLt
        omega
      · rfl
    have h0 : y p (topIdx j s) = 0 := hy hlt
    simp [h0]

/-! ## Equivariance of minor monomials -/

/-- The weight `l_i = d + ∑_{j : n - (j + 1) ≤ i} c_j` of the minor monomial `minorMonomial c d`
at the position `i`: left multiplication by an upper triangular `b` multiplies it by
`∏_i b_ii^{l_i}`. The weights do not decrease along the positions. -/
def minorWeight (c : Fin n → ℕ) (d : ℤ) (i : Fin n) : ℤ :=
  d + ∑ j ∈ univ.filter (fun j : Fin n => n - (j + 1) ≤ (i : ℕ)), (c j : ℤ)

theorem prod_botIdx (j : Fin n) (f : Fin n → ℂ) :
    ∏ t, f (botIdx j t) = ∏ i ∈ bot j, f i := by
  rw [bot, prod_map]
  rfl

/-- **Left equivariance.** For `b` upper triangular with nonzero diagonal entries,
`minorMonomial c d (b g) = ∏_i b_ii^{l_i} · minorMonomial c d g`. -/
theorem minorMonomial_upper_mul (c : Fin n → ℕ) (d : ℤ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsUpperTriangular) (hdiag : ∀ i, b i i ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ) :
    minorMonomial c d (b * g) = (∏ i, b i i ^ minorWeight c d i) * minorMonomial c d g := by
  unfold minorMonomial
  simp_rw [minor_upper_mul _ hb g, mul_pow, prod_mul_distrib]
  rw [det_mul, det_of_isUpperTriangular hb, mul_zpow]
  have key : (∏ i, b i i) ^ d * ∏ j, (∏ t, b (botIdx j t) (botIdx j t)) ^ c j =
      ∏ i, b i i ^ minorWeight c d i := by
    simp_rw [prod_botIdx _ (fun i => b i i), ← prod_pow]
    rw [prod_comm' (t' := univ) (s' := fun i => univ.filter fun j : Fin n => i ∈ bot j)
      (fun j i => by simp)]
    rw [← prod_zpow, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [prod_pow_eq_pow_sum, minorWeight, zpow_add₀ (hdiag i), ← zpow_natCast]
    congr 2
    push_cast
    refine sum_congr ?_ fun _ _ => rfl
    ext j
    simp [mem_bot]
  rw [← key]
  ring

/-- The right character: `rightChar c d y = det(y)^d ∏_j (∏_{t ≤ j} y_tt)^{c_j}`. -/
def rightChar (c : Fin n → ℕ) (d : ℤ) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  y.det ^ d * ∏ j, (∏ t, y (topIdx j t) (topIdx j t)) ^ c j

/-- **Right equivariance.** For `y` upper triangular,
`minorMonomial c d (g y) = minorMonomial c d g · rightChar c d y`. -/
theorem minorMonomial_mul_upper (c : Fin n → ℕ) (d : ℤ) (g : Matrix (Fin n) (Fin n) ℂ)
    {y : Matrix (Fin n) (Fin n) ℂ} (hy : y.IsUpperTriangular) :
    minorMonomial c d (g * y) = minorMonomial c d g * rightChar c d y := by
  unfold minorMonomial rightChar
  simp_rw [minor_mul_upper _ g hy, mul_pow, prod_mul_distrib]
  rw [det_mul, mul_zpow]
  ring

/-! ## Smoothness -/

/-- The minor monomial as a function on `GL_n(ℂ)`. -/
def minorFun (c : Fin n → ℕ) (d : ℤ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  minorMonomial c d (g : Matrix (Fin n) (Fin n) ℂ)

theorem contDiff_submatrix {m : ℕ} (r s : Fin m → Fin n) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y.submatrix r s) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun y => y.submatrix r s, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiff_minor (j : Fin n) : ContDiff ℝ ∞ (minor j) :=
  ComplexMaximalParabolicIntegration.contDiff_det.comp (contDiff_submatrix _ _)

theorem contDiffOn_det_zpow (d : ℤ) :
    ContDiffOn ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y.det ^ d) {y | IsUnit y} := by
  have hdet : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y.det) :=
    ComplexMaximalParabolicIntegration.contDiff_det
  rcases d with m | m
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (hdet.pow m).contDiffOn
  · simp only [zpow_negSucc]
    refine (hdet.pow (m + 1)).contDiffOn.inv fun y hy => ?_
    exact pow_ne_zero _ ((Matrix.isUnit_iff_isUnit_det y).1 hy).ne_zero

theorem contDiffOn_minorMonomial (c : Fin n → ℕ) (d : ℤ) :
    ContDiffOn ℝ ∞ (minorMonomial c d) {y | IsUnit y} :=
  (contDiffOn_det_zpow d).mul
    (contDiff_prod fun j _ => (contDiff_minor j).pow (c j)).contDiffOn

/-- The minor monomial is smooth on `GL_n(ℂ)`. -/
theorem contMDiff_minorFun (c : Fin n → ℕ) (d : ℤ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (minorFun c d) :=
  contMDiff_of_contDiffOn (contDiffOn_minorMonomial c d) fun _ => rfl

/-! ## Right derivatives along upper triangular directions -/

theorem isUpperTriangular_one_add_smul {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsUpperTriangular) (t : ℝ) : (1 + t • X).IsUpperTriangular := by
  intro i j hij
  have hne : i ≠ j := (ne_of_lt hij).symm
  simp [Matrix.one_apply_ne hne, hX hij]

/-- The infinitesimal right character: the derivative at `0` of `t ↦ rightChar c d (1 + t X)`. -/
def rightCharDeriv (c : Fin n → ℕ) (d : ℤ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  deriv (fun t : ℝ => rightChar c d (1 + t • X)) 0

/-- **Right derivatives.** For `X` upper triangular, `R(X) v = c_X · v` with
`c_X = rightCharDeriv c d X`. -/
theorem rightDerivative_minorFun {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsUpperTriangular)
    (c : Fin n → ℕ) (d : ℤ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (minorFun c d) g =
      rightCharDeriv c d X * minorFun c d g := by
  rw [rightDerivative_eq_fderiv (contMDiff_minorFun c d) X g]
  have hF : HasFDerivAt (unitsExtension (minorFun c d))
      (fderiv ℝ (unitsExtension (minorFun c d)) (g : Matrix (Fin n) (Fin n) ℂ))
      (g : Matrix (Fin n) (Fin n) ℂ) :=
    ((contDiffAt_unitsExtension (contMDiff_minorFun c d) g).differentiableAt
      (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => (g : Matrix (Fin n) (Fin n) ℂ) +
      t • ((g : Matrix (Fin n) (Fin n) ℂ) * X)) ((g : Matrix (Fin n) (Fin n) ℂ) * X) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      ((g : Matrix (Fin n) (Fin n) ℂ) * X)).const_add (g : Matrix (Fin n) (Fin n) ℂ)
  have hcomp := hF.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [← hcomp.deriv]
  have hunit : ∀ᶠ t in nhds (0 : ℝ),
      IsUnit ((g : Matrix (Fin n) (Fin n) ℂ) + t • ((g : Matrix (Fin n) (Fin n) ℂ) * X)) :=
    hline.continuousAt.preimage_mem_nhds
      (isOpen_setOf_isUnit_matrix.mem_nhds (by simp))
  have heq : (unitsExtension (minorFun c d) ∘ fun t : ℝ => (g : Matrix (Fin n) (Fin n) ℂ) +
      t • ((g : Matrix (Fin n) (Fin n) ℂ) * X)) =ᶠ[nhds 0]
      fun t => minorFun c d g * rightChar c d (1 + t • X) := by
    filter_upwards [hunit] with t ht
    simp only [Function.comp_apply, unitsExtension, dif_pos ht, minorFun, IsUnit.unit_spec]
    rw [show (g : Matrix (Fin n) (Fin n) ℂ) + t • ((g : Matrix (Fin n) (Fin n) ℂ) * X) =
      (g : Matrix (Fin n) (Fin n) ℂ) * (1 + t • X) by rw [mul_add, mul_one, mul_smul_comm]]
    exact minorMonomial_mul_upper c d _ (isUpperTriangular_one_add_smul hX t)
  rw [heq.deriv_eq, deriv_const_mul_field, rightCharDeriv, mul_comm]

/-! ## `U(n)`-finiteness -/

open RealPolynomialFunctions LevelFunctions

theorem minor_mem_degLE (j : Fin n) :
    (fun v => minor j (toMat v)) ∈ degLE (Fin n × Fin n) n := by
  have : (fun v => minor j (toMat v)) = ∑ σ : Equiv.Perm (Fin (j + 1)),
      (Equiv.Perm.sign σ : ℤ) • ∏ t : Fin (j + 1),
        coord (Fin n × Fin n) ((botIdx j (σ t), topIdx j t), false) := by
    funext v
    simp only [minor, Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def]
    rfl
  rw [this]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_of_tower_mem _ _ ?_
  have := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
    (fun t : Fin (j + 1) => coord (Fin n × Fin n) ((botIdx j (σ t), topIdx j t), false))
    (fun _ => 1) fun t _ => coord_mem_degLE _
  refine degLE_mono ?_ this
  simp

/-- The polynomial part `∏_j Δ_{j+1}^{c_j}` of the minor monomial, in the entries. -/
def minorPoly (c : Fin n → ℕ) (v : Fin n × Fin n → ℂ) : ℂ :=
  ∏ j, minor j (toMat v) ^ c j

theorem minorPoly_mem_degLE (c : Fin n → ℕ) :
    minorPoly c ∈ degLE (Fin n × Fin n) (∑ j, c j * n) := by
  have := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
    (fun j : Fin n => (fun v => minor j (toMat v)) ^ c j) (fun j => c j * n)
    fun j _ => pow_mem_degLE (minor_mem_degLE j) (c j)
  convert this using 1
  funext v
  simp [minorPoly, Finset.prod_apply]

/-- Right multiplication by `k` on entry vectors. -/
def rightMulEntries (k : Matrix (Fin n) (Fin n) ℂ) (v : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  ofMat (toMat v * k)

theorem coord_rightMulEntries_mem_degLE (k : Matrix (Fin n) (Fin n) ℂ) (c : (Fin n × Fin n) × Bool) :
    coord (Fin n × Fin n) c ∘ rightMulEntries k ∈ degLE (Fin n × Fin n) 1 := by
  refine coord_comp_mem_degLE (fun p => ?_) c
  have : (fun v => rightMulEntries k v p) =
      ∑ r : Fin n, k r p.2 • coord (Fin n × Fin n) ((p.1, r), false) := by
    funext v
    simp [rightMulEntries, ofMat, toMat, Matrix.mul_apply, coord, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (coord_mem_degLE _)

/-- Multiplication by `det^d`, on functions of the entries. -/
def detWeightMap (d : ℤ) : ((Fin n × Fin n → ℂ) → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun P g := (g : Matrix (Fin n) (Fin n) ℂ).det ^ d * P (ofMat (g : Matrix (Fin n) (Fin n) ℂ))
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' a P := by funext g; simp [mul_left_comm]

theorem rightTranslation_minorFun (c : Fin n → ℕ) (d : ℤ) (k : Langlands.GeneralLinear n ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k (minorFun c d) =
      (k : Matrix (Fin n) (Fin n) ℂ).det ^ d •
        detWeightMap d (minorPoly c ∘ rightMulEntries (k : Matrix (Fin n) (Fin n) ℂ)) := by
  funext g
  change minorMonomial c d ((g * k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) = _
  simp only [Pi.smul_apply, smul_eq_mul, detWeightMap, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, minorPoly, rightMulEntries, toMat_ofMat, Units.val_mul, minorMonomial,
    Matrix.det_mul, mul_zpow]
  ring

/-- **`U(n)`-finiteness.** The minor monomial is `U(n)`-finite for right translation. -/
theorem minorFun_mem_kFiniteVectors (c : Fin n → ℕ) (d : ℤ) :
    minorFun c d ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff]
  refine Submodule.finiteDimensional_of_le
    (S₂ := (degLE (Fin n × Fin n) ((∑ j, c j * n) * 1)).map (detWeightMap d)) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
    (minorFun c d) ∈ _
  rw [rightTranslation_minorFun]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem
    (comp_mem_degLE (minorPoly_mem_degLE c) (coord_rightMulEntries_mem_degLE _)))

/-- Products of `U(n)`-finite functions are `U(n)`-finite. -/
theorem mul_mem_kFiniteVectors {f h : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n))
    (hh : h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n)) :
    f * h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff] at hf hh ⊢
  set S₁ := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ) f)
  set S₂ := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ) h)
  have hfg : (S₁ * S₂).FG :=
    ((Submodule.fg_iff_finiteDimensional S₁).2 hf).mul ((Submodule.fg_iff_finiteDimensional S₂).2 hh)
  have : FiniteDimensional ℂ (S₁ * S₂) := (Submodule.fg_iff_finiteDimensional _).1 hfg
  refine Submodule.finiteDimensional_of_le (S₂ := S₁ * S₂) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)

/-! ## Nonvanishing at the antidiagonal permutation matrix -/

/-- The antidiagonal permutation matrix (`P i j = 1` exactly when `j = n - 1 - i`), as a unitary
matrix. -/
def revUnitary (n : ℕ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ComplexPermutation.permUnitary Fin.revPerm

theorem submatrix_revPerm (j : Fin n) :
    ((Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℂ).submatrix (botIdx j) (topIdx j) =
      (Fin.revPerm : Equiv.Perm (Fin (j + 1))).permMatrix ℂ := by
  ext t t'
  simp only [Matrix.submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
  have hiff : Fin.rev (botIdx j t) = topIdx j t' ↔ Fin.rev t = t' := by
    simp only [Fin.ext_iff, Fin.val_rev, botIdx, topIdx]
    have := t.isLt; have := t'.isLt; have := j.isLt
    omega
  simp only [hiff]

theorem minor_revPerm_ne_zero (j : Fin n) :
    minor j ((Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℂ) ≠ 0 := by
  rw [minor, submatrix_revPerm, Matrix.det_permutation]
  exact Int.cast_ne_zero.2 (Units.ne_zero _)

/-- The minor monomial does not vanish at the antidiagonal permutation matrix. -/
theorem minorMonomial_revUnitary_ne_zero (c : Fin n → ℕ) (d : ℤ) :
    minorMonomial c d ((revUnitary n : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  rw [revUnitary, ComplexPermutation.permUnitary_coe, minorMonomial]
  refine mul_ne_zero (zpow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun j _ =>
    pow_ne_zero _ (minor_revPerm_ne_zero j))
  rw [Matrix.det_permutation]
  exact Int.cast_ne_zero.2 (Units.ne_zero _)

end ComplexMinorProduct

end Langlands.Archimedean
