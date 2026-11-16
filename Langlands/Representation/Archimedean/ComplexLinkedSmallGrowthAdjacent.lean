import Langlands.Representation.Archimedean.ComplexSmallGrowthTools
import Langlands.Representation.Archimedean.ComplexNoncompactDimension
import Langlands.Representation.Archimedean.ComplexLevelSpan
import Langlands.Representation.Archimedean.ComplexLevelBlockPolynomial

/-!
# Small growth for an adjacent linked pair

Let `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` and suppose that the characters at the adjacent
positions `i`, `i + 1` satisfy `χ_{i+1} = χ_i · z^p z̄^q` with `p, q ≥ 1`, that is
`l_{i+1} - l_i = p - q` and `t_{i+1} - t_i = (p + q)/2`. Then `SmallGrowth n χ` holds
(`smallGrowth_adjacent`):

* `E` is the span of the level products (`LevelFunctions.levelSpan`) for the level data
  `e_m = l_m - l_{m-1}` (`h_m = e_m⁺` holomorphic, `b_m = e_m⁻` antiholomorphic determinant
  factors, modulus increments `τ_m - τ_{m-1}`), except at the level `r = i + 1`, which gets
  `p - 1` holomorphic and `q - 1` antiholomorphic factors and no Gram factor. It is a nonzero
  finite-dimensional `U(n)`-stable space of `U(n)`-finite principal-series functions.
* In the noncompact picture, with the Gram weights `T_m(v) = det(Y_m Y_mᴴ)` of the lower rows
  of the lower unipotent element `nbMat v` and `σ_m` the Gram exponents, `E` lies in level `0`
  of `NoncompactPicture.filtrationLevel`; right derivatives raise the level by one, so
  `U_d(𝔤) · E` lies in level `d`, of dimension `≤ |S| (c (d + 1) + 1)^{n(n-1)-2}`.
-/

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean.AdjacentGrowth

open Langlands.GeneralLinear Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.BlockPolynomial Langlands.Archimedean.LevelFunctions
open Langlands.Archimedean.NoncompactPicture Langlands.Archimedean.SmallGrowthTools
open Langlands.Archimedean.ComplexDuality Langlands.Archimedean.FiniteFunctionSpaces
open Langlands.Archimedean.ComplexLinkedLanglandsQuotientGrowth

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ## Gram weights in the noncompact picture -/

/-- The Gram determinant of the rows `m, …, n-1` of `nbMat v`. -/
def gramWeight (m : Fin n) (v : Lw n → ℂ) : ℂ := tailGram (m : ℕ) (nbMat v)

theorem gramWeight_mem_degLE (m : Fin n) : gramWeight m ∈ degLE (Lw n) (2 * n) := by
  have h1 : IsPolyMat (ι := Lw n) 1 (fun v => tailRows (m : ℕ) (nbMat v)) :=
    fun a c => isPolyMat_nbMat (a : Fin n) c
  have h2 := (h1.mul h1.conjTranspose).det
  refine degLE_mono ?_ h2
  have := Fintype.card_subtype_le (fun j : Fin n => (m : ℕ) ≤ (j : ℕ))
  simp only [Fintype.card_fin] at this
  omega

theorem isPosReal_gramWeight (m : Fin n) : IsPosReal (gramWeight m) := fun v =>
  ⟨gramMinor (m : ℕ) (nbMat v), gramMinor_pos (m : ℕ) (nbUnit v),
    (ofReal_gramMinor (m : ℕ) (nbUnit v)).symm⟩

variable (h b : ℕ → ℕ) (dτ : ℕ → ℂ)

/-- The Gram exponents. -/
def gramExp (m : Fin n) : ℂ := dτ m - ((h m + b m : ℕ) : ℂ) / 2

theorem levelProduct_nbUnit (A : LevelMatrices n h b) (v : Lw n → ℂ) :
    levelProduct h b dτ A (nbUnit v) =
      (∏ m : Fin n, gramWeight m v ^ gramExp h b dτ m) *
        ∏ m : Fin n, detPart h b m (A m) (nbMat v) := by
  simp only [levelProduct, levelProductExt, Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun m _ => ?_
  simp only [gramPart, gramWeight, gramExp]
  rw [ofReal_gramMinor (m : ℕ) (nbUnit v)]
  rfl

theorem detProduct_mem_degLE (A : LevelMatrices n h b) :
    (fun v => ∏ m : Fin n, detPart h b m (A m) (nbMat v)) ∈ degLE (Lw n) (detDegree n h b) := by
  have hP := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
    (fun m : Fin n => fun w => detPart h b m (A m) (toMat w)) (fun m => (h m + b m) * n)
    fun m _ => detPart_mem_degLE h b m (A m)
  have hf : (∏ m : Fin n, fun w => detPart h b m (A m) (toMat w)) =
      fun w => ∏ m : Fin n, detPart h b m (A m) (toMat w) := by
    funext w; simp [Finset.prod_apply]
  rw [hf] at hP
  have hW : ∀ c, coord (Fin n × Fin n) c ∘ (fun v : Lw n → ℂ => ofMat (nbMat v)) ∈
      degLE (Lw n) 1 :=
    coord_comp_mem_degLE fun ab => isPolyMat_nbMat ab.1 ab.2
  have := comp_mem_degLE hP hW
  rw [mul_one] at this
  have heq : ((fun w => ∏ m : Fin n, detPart h b m (A m) (toMat w)) ∘
      fun v : Lw n → ℂ => ofMat (nbMat v)) = fun v => ∏ m : Fin n, detPart h b m (A m) (nbMat v) := by
    funext v
    simp only [Function.comp_apply, toMat_ofMat]
  rw [heq] at this
  exact this

/-- **The level span lies in level `0` of the filtration.** -/
theorem levelSpan_le_filtrationLevel {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    (hl : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k)
    (hτ : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m =
      t k + ((n : ℂ) - 1) / 2 - (k : ℕ))
    {i r : Fin n} (hir : i ≠ r) (hr : (r : ℕ) = (i : ℕ) + 1) {p q : ℕ}
    (hgram : dτ r - ((h r + b r : ℕ) : ℂ) / 2 = 0) (hp : h r < p) (hq : b r < q) {c : ℕ}
    (hc : detDegree n h b ≤ c) :
    levelSpan (n := n) h b dτ ≤
      filtrationLevel χ hir p q gramWeight (gramExp h b dτ) c 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨A, rfl⟩
  refine ⟨levelProduct_mem_principalSeries h b dτ l t hχ hl hτ A,
    isBlockPoly_levelProduct h b dτ hr hir hgram hp hq A,
    fun v => ∏ m : Fin n, detPart h b m (A m) (nbMat v),
    degLE_mono (by omega) (detProduct_mem_degLE h b A), fun v => ?_⟩
  rw [pow_zero, mul_one, levelProduct_nbUnit]

/-! ## Telescoping sums -/

theorem sum_filter_le_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (k : Fin n) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), g m =
      ∑ m ∈ Finset.range (k + 1), g m := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun m => if m ≤ (k : ℕ) then g m else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  have := k.2
  omega

/-- `f` shifted by one, with `0` at `0`. -/
def shift {M : Type*} [Zero M] (f : ℕ → M) (m : ℕ) : M := if m = 0 then 0 else f (m - 1)

theorem sum_range_sub_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (k : ℕ) :
    ∑ m ∈ Finset.range (k + 1), (f m - shift f m) = f k := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp [shift]

/-! ## The adjacent case -/

/-- **Small growth for an adjacent linked pair.** -/
theorem smallGrowth_adjacent {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    (i : ℕ) (hi : i + 1 < n) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hl : l (i + 1) - l i = (p : ℤ) - q) (ht : t (i + 1) - t i = ((p : ℂ) + q) / 2) :
    SmallGrowth n χ := by
  classical
  -- level data
  set e : ℕ → ℤ := fun m => l m - shift l m with he
  set τ : ℕ → ℂ := fun k => t k + ((n : ℂ) - 1) / 2 - (k : ℂ) with hτdef
  set dτ : ℕ → ℂ := fun m => τ m - shift τ m with hdτ
  set h : ℕ → ℕ := fun m => if m = i + 1 then p - 1 else (e m).toNat with hh
  set b : ℕ → ℕ := fun m => if m = i + 1 then q - 1 else (-e m).toNat with hb
  have hhb : ∀ m, (h m : ℤ) - b m = e m := by
    intro m
    by_cases hm : m = i + 1
    · subst hm
      simp only [hh, hb, ite_true, he, shift, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
      push_cast [Nat.cast_sub hp, Nat.cast_sub hq]
      linear_combination -hl
    · simp only [hh, hb, hm, ite_false]
      exact Int.toNat_sub_toNat_neg (e m)
  have hlsum : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k := by
    intro k
    rw [sum_filter_le_eq (fun m => (h m : ℤ) - b m) k]
    simp only [hhb, he]
    exact sum_range_sub_shift l k
  have hτsum : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m =
      t k + ((n : ℂ) - 1) / 2 - (k : ℕ) := by
    intro k
    rw [sum_filter_le_eq dτ k]
    exact sum_range_sub_shift τ k
  -- the root positions
  set i' : Fin n := ⟨i, by omega⟩
  set r : Fin n := ⟨i + 1, hi⟩
  have hr : (r : ℕ) = (i' : ℕ) + 1 := rfl
  have hir : i' ≠ r := fun heq => by simpa [i', r] using congrArg Fin.val heq
  have hlt : i' < r := Fin.mk_lt_mk.2 (by omega)
  have hhr : h r = p - 1 := by simp [hh, r]
  have hbr : b r = q - 1 := by simp [hb, r]
  have hgram : dτ r - ((h r + b r : ℕ) : ℂ) / 2 = 0 := by
    rw [hhr, hbr]
    simp only [hdτ, hτdef, shift, r, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    push_cast [Nat.cast_sub hp, Nat.cast_sub hq]
    linear_combination ht
  have hpr : h r < p := by omega
  have hqr : b r < q := by omega
  -- the filtration
  set σ := gramExp h b dτ
  set c : ℕ := (n + 1) + (n + 2) + n * (2 * n) + detDegree n h b
  set W : ℕ → Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
    fun N => filtrationLevel χ hir p q gramWeight σ c N
  have hTdeg : ∀ m : Fin n, gramWeight m ∈ degLE (Lw n) (2 * n) := gramWeight_mem_degLE
  have hcard : Fintype.card (Fin n) * (2 * n) ≤ c := by
    simp only [Fintype.card_fin, c]; omega
  have hmono : ∀ N, W N ≤ W (N + 1) := fun N =>
    filtrationLevel_mono (hir := hir) (p := p) (q := q) (σ := σ) (c := c) hTdeg hcard N
  have hstep : ∀ N (f : Langlands.GeneralLinear n ℂ → ℂ), f ∈ W N →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, rightDerivative (matrixModel ℂ n) X f ∈ W (N + 1) :=
    fun N f hf X => rightDerivative_mem_filtrationLevel (hir := hir) (p := p) (q := q) (σ := σ)
      (c := c) l t hχ hTdeg isPosReal_gramWeight (by simp only [Fintype.card_fin, c]; omega) hf X
  obtain ⟨S, -, hS⟩ := exists_finset_eval_injective _ (bidegLT p q) rfl
  have hdim := fun N => finrank_filtrationLevel_le hir hlt gramWeight σ χ p q c
    isPosReal_gramWeight S hS N
  -- the subspace E
  set KF := kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)
  have hLK : levelSpan (n := n) h b dτ ≤ KF := levelSpan_le_kFiniteFunctions h b dτ l t hχ hlsum hτsum
  set E : Submodule ℂ KF := (levelSpan (n := n) h b dτ).comap KF.subtype
  have hEW : E ≤ levelIn (χ := χ) W 0 := fun e he =>
    levelSpan_le_filtrationLevel h b dτ l t hχ hlsum hτsum hir hr hgram hpr hqr
      (by simp only [c]; omega) he
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · -- E ≠ ⊥
    intro hbot
    set f₀ := levelProduct h b dτ (selectMatrices h b)
    have hf₀ : f₀ ∈ levelSpan (n := n) h b dτ := Submodule.subset_span ⟨_, rfl⟩
    have hmem : (⟨f₀, hLK hf₀⟩ : KF) ∈ E := hf₀
    rw [hbot, Submodule.mem_bot] at hmem
    have h1 := congrArg (fun x : KF => (x : Langlands.GeneralLinear n ℂ → ℂ) 1) hmem
    simp only [Submodule.coe_zero, Pi.zero_apply] at h1
    rw [show f₀ 1 = 1 from levelProduct_tailSelect_one h b dτ] at h1
    exact one_ne_zero h1
  · -- E is finite-dimensional
    let Φ : E →ₗ[ℂ] levelSpan (n := n) h b dτ :=
      LinearMap.codRestrict _ (KF.subtype.comp E.subtype) fun x => x.2
    refine Module.Finite.of_injective Φ fun x y hxy => ?_
    have := congrArg (fun z : levelSpan (n := n) h b dτ => (z : Langlands.GeneralLinear n ℂ → ℂ))
      hxy
    exact Subtype.ext (Subtype.ext this)
  · -- E is `U(n)`-stable
    intro k e he
    change ((principalSeriesRep ℂ n χ k e : KF) : Langlands.GeneralLinear n ℂ → ℂ) ∈
      levelSpan (n := n) h b dτ
    rw [principalSeriesRep_apply_coe]
    exact rightTranslation_mem_levelSpan h b dτ he k.2
  · -- the growth bound
    refine ⟨(S.card * (c + 1) ^ (n * (n - 1) - 2) : ℕ), fun d => ?_⟩
    have := (hdim d).1
    have h1 := finrank_filtrationSpan_le W hmono hstep E hEW d
    have h2 := (hdim d).2
    have h3 : (c * (d + 1) + 1) ^ (n * (n - 1) - 2) ≤
        (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1) := by
      calc (c * (d + 1) + 1) ^ (n * (n - 1) - 2)
          ≤ ((c + 1) * (d + 1)) ^ (n * (n - 1) - 2) :=
            Nat.pow_le_pow_left (by nlinarith) _
        _ = (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 2) := mul_pow _ _ _
        _ ≤ (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
    have h4 : Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ) d E) ≤
        S.card * (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1) := by
      calc _ ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ S.card * ((c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1)) :=
            Nat.mul_le_mul_left _ h3
        _ = S.card * (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1) := by ring
    have h5 : ((S.card * (c + 1) ^ (n * (n - 1) - 2) * (d + 1) ^ (n * (n - 1) - 1) : ℕ) : ℝ) =
        ((S.card * (c + 1) ^ (n * (n - 1) - 2) : ℕ) : ℝ) * ((d : ℝ) + 1) ^ (n * (n - 1) - 1) := by
      push_cast; ring
    rw [← h5]
    exact_mod_cast h4

end Langlands.Archimedean.AdjacentGrowth
