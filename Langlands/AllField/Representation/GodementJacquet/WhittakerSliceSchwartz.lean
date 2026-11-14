import Langlands.Representation.GodementJacquet.WhittakerSliceSchwartz
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Unipotent slices of matrix test functions are Schwartz–Bruhat

For a p-adic field, a nontrivial additive character `ψ` and a compactly
supported locally constant function `f` on all square matrices, the function
`x ↦ ∫_N f(u · diag(x)) ψ(u) du` on `F^(n+1)` is Schwartz–Bruhat. See the
paired Markdown for the route.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerSlice
open Langlands.GodementJacquet.WhittakerSlice hiding adjacentTransvection column_bound continuous_nabs eventually_small_scalar exists_character_ne_one exists_small_matrix exists_support_bound exists_uniform_constancy mul_adjacentTransvection_val nabs nabs_add_le_max nabs_mul nabs_neg nabs_nonneg nabs_one nabs_pos nabs_zero rightMulHomeomorph sliceIntegral sliceIntegral_eq_zero_of_invariant sliceIntegral_eq_zero_of_lt_threshold sliceIntegral_eq_zero_step sliceIntegral_hasCompactSupport sliceIntegral_isLocallyConstant sliceIntegral_mem sliceIntegral_rightTranslate_mem sliceLocalField sliceTopology sliceValuativeRel standardCharacter_adjacentTransvection
open Langlands.AllField.GodementJacquet.WhittakerSlice
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory Filter _root_.Topology
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uX

section Topological


end Topological

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The canonical residue-normalized absolute value. -/
abbrev nabs (x : F) : ℝ := (⟨⟩ : LocalFieldData F).normalizedAbs x

variable {F}

theorem nabs_nonneg (x : F) : 0 ≤ nabs F x :=
  (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg x

theorem nabs_mul (x y : F) : nabs F (x * y) = nabs F x * nabs F y :=
  (⟨⟩ : LocalFieldData F).normalizedAbs_mul x y

theorem nabs_add_le_max (x y : F) :
    nabs F (x + y) ≤ max (nabs F x) (nabs F y) :=
  (⟨⟩ : LocalFieldData F).normalizedAbs_add_le_max x y

theorem nabs_neg (x : F) : nabs F (-x) = nabs F x :=
  (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).map_neg x

theorem nabs_zero : nabs F 0 = 0 := (⟨⟩ : LocalFieldData F).normalizedAbs_zero

theorem nabs_one : nabs F 1 = 1 := (⟨⟩ : LocalFieldData F).normalizedAbs_one

theorem nabs_pos {x : F} (hx : x ≠ 0) : 0 < nabs F x :=
  (⟨⟩ : LocalFieldData F).normalizedAbs_pos hx

theorem continuous_nabs : Continuous (nabs F) :=
  Langlands.LocalFieldData.continuous_normalizedAbs (⟨⟩ : LocalFieldData F)

/-- Small absolute value eventually lands in every neighbourhood of zero. -/
theorem eventually_small_scalar :
    ∀ s ∈ 𝓝 (0 : F), ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z, nabs F z < r → z ∈ s := by
  intro s hs
  obtain ⟨t, ⟨a, ε, hε, rfl⟩, h0t, hts⟩ :=
    ((⟨⟩ : LocalFieldData F).normalizedAbs_balls_basis.mem_nhds_iff).1 hs
  have ha : nabs F a < ε := by
    have h0t' : (⟨⟩ : LocalFieldData F).normalizedAbs (0 - a) < ε := h0t
    rwa [zero_sub, show (⟨⟩ : LocalFieldData F).normalizedAbs (-a) = nabs F a from
      nabs_neg a] at h0t'
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr z hz
  apply hts
  show (⟨⟩ : LocalFieldData F).normalizedAbs (z - a) < ε
  rw [sub_eq_add_neg]
  exact (nabs_add_le_max z (-a)).trans_lt
    (max_lt (hz.trans hr.2) (by rw [nabs_neg]; exact ha))

/-- Entrywise small matrices lie in every neighbourhood of zero. -/
theorem exists_small_matrix {ι : Type*} [Finite ι]
    {s : Set (Matrix ι ι F)} (hs : s ∈ 𝓝 (0 : Matrix ι ι F)) :
    ∃ r > 0, ∀ δ : Matrix ι ι F, (∀ a b, nabs F (δ a b) < r) → δ ∈ s := by
  have hrow : ∀ a : ι, ∀ t ∈ 𝓝 ((0 : ι → ι → F) a),
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : ι → F, (∀ b, nabs F (z b) < r) → z ∈ t :=
    fun a => pi_eventually_small (0 : ι → F) (fun _ r z => nabs F z < r)
      (fun _ => eventually_small_scalar)
  have hmat := pi_eventually_small (0 : ι → ι → F)
    (fun _ r z => ∀ b, nabs F (z b) < r) hrow s hs
  obtain ⟨r, hr, hpos⟩ := (hmat.and self_mem_nhdsWithin).exists
  exact ⟨r, hpos, fun δ hδ => hr δ hδ⟩

/-- A compactly supported locally constant function on square matrices is
invariant under all entrywise sufficiently small perturbations. -/
theorem exists_uniform_constancy {ι : Type*} [Fintype ι] (f : Matrix ι ι F → ℂ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ r > 0, ∀ M δ : Matrix ι ι F, (∀ a b, nabs F (δ a b) < r) →
      f (M + δ) = f M := by
  obtain ⟨U, hU, hinv⟩ := exists_nhds_add_invariant f hf hc
  obtain ⟨r, hr, hsmall⟩ := exists_small_matrix hU
  exact ⟨r, hr, fun M δ hδ => hinv M δ (hsmall δ hδ)⟩

/-- Comparison of two values of such a function: it suffices that the entrywise
difference is small whenever one of the two values is nonzero. -/
theorem eq_of_small_diff {ι : Type*} {f : Matrix ι ι F → ℂ} {r : ℝ}
    (hr : ∀ M δ : Matrix ι ι F, (∀ a b, nabs F (δ a b) < r) → f (M + δ) = f M)
    {A A' : Matrix ι ι F}
    (h : f A ≠ 0 ∨ f A' ≠ 0 → ∀ a b, nabs F (A' a b - A a b) < r) : f A' = f A := by
  by_cases hA : f A ≠ 0
  · have e := hr A (A' - A) (h (Or.inl hA))
    rwa [add_sub_cancel] at e
  by_cases hA' : f A' ≠ 0
  · have e := hr A' (A - A') (fun a b => by
      rw [Matrix.sub_apply, ← nabs_neg, neg_sub]
      exact h (Or.inr hA') a b)
    rw [add_sub_cancel] at e
    exact e.symm
  · rw [not_not.1 hA, not_not.1 hA']

/-- The entries of the matrices in the support of a compactly supported function
are uniformly bounded. -/
theorem exists_support_bound {ι : Type*} [Fintype ι] (f : Matrix ι ι F → ℂ)
    (hc : HasCompactSupport f) :
    ∃ R, ∀ M, f M ≠ 0 → ∀ a b, nabs F (M a b) ≤ R := by
  have hcont : Continuous fun M : Matrix ι ι F => ∑ a, ∑ b, nabs F (M a b) :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_nabs.comp (continuous_id.matrix_elem a b)
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove_image hcont.continuousOn
  refine ⟨R, fun M hM a b => ?_⟩
  have hsum : ∑ a, ∑ b, nabs F (M a b) ≤ R := hR ⟨M, subset_tsupport f hM, rfl⟩
  calc nabs F (M a b) ≤ ∑ b', nabs F (M a b') :=
        Finset.single_le_sum (f := fun b' => nabs F (M a b')) (fun b' _ => nabs_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', nabs F (M a' b') :=
        Finset.single_le_sum (f := fun a' => ∑ b', nabs F (M a' b'))
          (fun a' _ => Finset.sum_nonneg fun _ _ => nabs_nonneg _) (Finset.mem_univ a)
    _ ≤ R := hsum

section Slice

open Langlands.GeneralLinear

variable {n : ℕ}

/-- A column of a unipotent upper triangular matrix is bounded once the column
scaled by `y` is bounded, provided `|y|` is bounded below away from the first
column. -/
theorem column_bound {u : upperUnipotent (n + 1) F} {b : Fin (n + 1)}
    {y : F} {R t : ℝ} (ht : 0 < t) (hy : b = 0 ∨ t ≤ nabs F y)
    (hR : ∀ a, nabs F (u.val a b * y) ≤ R) (a : Fin (n + 1)) :
    nabs F (u.val a b) ≤ max 1 (R / t) := by
  rcases lt_trichotomy b a with hba | rfl | hab
  · rw [UpperUnipotent.entry_eq_zero u hba, nabs_zero]
    exact zero_le_one.trans (le_max_left _ _)
  · rw [UpperUnipotent.entry_diag, nabs_one]
    exact le_max_left _ _
  · rcases hy with rfl | hty
    · exact absurd hab (Fin.not_lt_zero a)
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ ht]
      have e := hR a
      rw [nabs_mul] at e
      exact (mul_le_mul_of_nonneg_left hty (nabs_nonneg _)).trans e

/-- The elementary unipotent matrix `1 + c E_(i,i+1)`. -/
def adjacentTransvection (i : Fin n) (c : F) : upperUnipotent (n + 1) F :=
  ⟨transvectionUnit i.castSucc i.succ i.castSucc_lt_succ.ne c, by
    refine ⟨fun {a b} hab => ?_, fun a => ?_⟩
    · replace hab : b < a := hab
      change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) + Matrix.single i.castSucc i.succ c) a b = 0
      rw [Matrix.add_apply, Matrix.one_apply_ne hab.ne', Matrix.single_apply_of_ne, zero_add]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 i.castSucc_lt_succ.le)
    · change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) + Matrix.single i.castSucc i.succ c) a a = 1
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, h⟩
      exact i.castSucc_lt_succ.ne h.symm⟩

/-- Right multiplication by `1 + c E_(i,i+1)` adds `c` times column `i` to
column `i+1`. -/
theorem mul_adjacentTransvection_val (u : upperUnipotent (n + 1) F) (i : Fin n)
    (c : F) :
    (u * adjacentTransvection i c).val.val =
      u.val.val * Matrix.transvection i.castSucc i.succ c := rfl

/-- The standard character takes the value `ψ(c)` on `1 + c E_(i,i+1)`. -/
theorem standardCharacter_adjacentTransvection (ψ : UnitaryAdditiveCharacter F)
    (i : Fin n) (c : F) :
    (standardCharacter ψ n (adjacentTransvection i c) : ℂ) = ψ.complex c := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) + Matrix.single i.castSucc i.succ c) i.castSucc i.succ = c
    rw [Matrix.add_apply, Matrix.one_apply_ne i.castSucc_lt_succ.ne,
      Matrix.single_apply_same, zero_add]
  · intro k _ hk
    change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) + Matrix.single i.castSucc i.succ c) k.castSucc k.succ = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne k.castSucc_lt_succ.ne,
      Matrix.single_apply_of_ne, zero_add]
    rintro ⟨h, -⟩
    exact hk (Fin.castSucc_injective _ h.symm)
  · intro h
    exact absurd (Finset.mem_univ i) h

variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]

variable (F) in
/-- The unipotent slice integral `x ↦ ∫_N f(u · diag(x)) ψ(u) du` for the
normalized Haar measure on the upper unipotent group. -/
def sliceIntegral (ψ : UnitaryAdditiveCharacter F)
    (f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ)
    (x : Fin (n + 1) → F) : ℂ :=
  ∫ u, f (u.val.val * Matrix.diagonal x) * (standardCharacter ψ n u : ℂ)
    ∂unipotentHaar F n

/-- If the integrand's test-function factor is invariant under right translation
by `1 + c E_(i,i+1)` with `ψ(c) ≠ 1`, the slice integral vanishes. -/
theorem sliceIntegral_eq_zero_of_invariant (ψ : UnitaryAdditiveCharacter F)
    (f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) (x : Fin (n + 1) → F)
    (i : Fin n) (c : F) (hc : ψ.complex c ≠ 1)
    (h : ∀ u : upperUnipotent (n + 1) F,
      f ((u * adjacentTransvection i c).val.val * Matrix.diagonal x) =
        f (u.val.val * Matrix.diagonal x)) :
    sliceIntegral F ψ f x = 0 := by
  have key : sliceIntegral F ψ f x = sliceIntegral F ψ f x * ψ.complex c := by
    calc sliceIntegral F ψ f x
        = ∫ u, f ((u * adjacentTransvection i c).val.val * Matrix.diagonal x) *
            (standardCharacter ψ n (u * adjacentTransvection i c) : ℂ)
            ∂unipotentHaar F n :=
          (integral_mul_right_eq_self
            (fun u : upperUnipotent (n + 1) F =>
              f (u.val.val * Matrix.diagonal x) * (standardCharacter ψ n u : ℂ))
            (adjacentTransvection i c)).symm
      _ = ∫ u, f (u.val.val * Matrix.diagonal x) * (standardCharacter ψ n u : ℂ) *
            ψ.complex c ∂unipotentHaar F n := by
          congr 1
          funext u
          rw [h u, map_mul, Units.val_mul, standardCharacter_adjacentTransvection, mul_assoc]
      _ = sliceIntegral F ψ f x * ψ.complex c := integral_mul_const _ _
  have e : sliceIntegral F ψ f x * (ψ.complex c - 1) = 0 := by
    rw [mul_sub, mul_one, ← key, sub_self]
  rcases mul_eq_zero.1 e with h0 | h1
  · exact h0
  · exact absurd (sub_eq_zero.1 h1) hc

/-- One vanishing step: if `|x_i| ≥ t` (or `i = 0`) and `|x_(i+1)|` is below the
threshold attached to `t`, the slice integral vanishes. -/
theorem sliceIntegral_eq_zero_step (ψ : UnitaryAdditiveCharacter F)
    {f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ} {r R : ℝ} (hr : 0 < r)
    (hconst : ∀ M δ : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
      (∀ a b, nabs F (δ a b) < r) → f (M + δ) = f M)
    (hsupp : ∀ M, f M ≠ 0 → ∀ a b, nabs F (M a b) ≤ R)
    {c : F} (hc : ψ.complex c ≠ 1) (hc0 : c ≠ 0) (i : Fin n) {t : ℝ} (ht : 0 < t)
    (x : Fin (n + 1) → F) (hx : i.castSucc = 0 ∨ t ≤ nabs F (x i.castSucc))
    (hsmall : nabs F (x i.succ) < r / (nabs F c * max 1 (R / t))) :
    sliceIntegral F ψ f x = 0 := by
  apply sliceIntegral_eq_zero_of_invariant ψ f x i c hc
  intro u
  have hne : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  have hcol' : ∀ a, (u.val.val * Matrix.transvection i.castSucc i.succ c) a i.castSucc =
      u.val a i.castSucc := fun a => Matrix.mul_transvection_apply_of_ne _ _ _ _ hne _ _
  apply eq_of_small_diff hconst
  intro hnz a b
  rw [mul_adjacentTransvection_val, Matrix.mul_diagonal, Matrix.mul_diagonal]
  have hcol : ∀ a, nabs F (u.val a i.castSucc * x i.castSucc) ≤ R := by
    intro a
    rcases hnz with h | h
    · have e := hsupp _ h a i.castSucc
      rwa [Matrix.mul_diagonal] at e
    · have e := hsupp _ h a i.castSucc
      rwa [mul_adjacentTransvection_val, Matrix.mul_diagonal, hcol'] at e
  have hm : 0 < nabs F c * max 1 (R / t) :=
    mul_pos (nabs_pos hc0) (one_pos.trans_le (le_max_left _ _))
  by_cases hb : b = i.succ
  · subst hb
    rw [Matrix.mul_transvection_apply_same, add_mul, add_sub_cancel_left, mul_assoc, nabs_mul,
      nabs_mul]
    have hu := column_bound ht hx hcol a
    calc nabs F c * (nabs F (u.val a i.castSucc) * nabs F (x i.succ))
        ≤ nabs F c * (max 1 (R / t) * nabs F (x i.succ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (nabs_nonneg _))
            (nabs_nonneg _)
      _ = (nabs F c * max 1 (R / t)) * nabs F (x i.succ) := by ring
      _ < r := (lt_div_iff₀' hm).1 hsmall
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hb, sub_self, nabs_zero]
    exact hr

/-- Vanishing by induction: for `b ≠ 0`, if `|x_b| < θ b` then the slice
integral vanishes. -/
theorem sliceIntegral_eq_zero_of_lt_threshold (ψ : UnitaryAdditiveCharacter F)
    {f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ} {r R : ℝ} (hr : 0 < r)
    (hconst : ∀ M δ : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
      (∀ a b, nabs F (δ a b) < r) → f (M + δ) = f M)
    (hsupp : ∀ M, f M ≠ 0 → ∀ a b, nabs F (M a b) ≤ R)
    {c : F} (hc : ψ.complex c ≠ 1) (hc0 : c ≠ 0) :
    ∀ (b : Fin (n + 1)), b ≠ 0 → ∀ x : Fin (n + 1) → F,
      nabs F (x b) < threshold r R (nabs F c) b.val → sliceIntegral F ψ f x = 0 := by
  have hθ := threshold_pos (R := R) hr (nabs_pos hc0)
  have main : ∀ k : ℕ, ∀ i : Fin n, i.val = k → ∀ x : Fin (n + 1) → F,
      nabs F (x i.succ) < threshold r R (nabs F c) (k + 1) → sliceIntegral F ψ f x = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi x hx
      exact sliceIntegral_eq_zero_step ψ hr hconst hsupp hc hc0 i one_pos x
        (Or.inl (Fin.ext (by simp [hi]))) hx
    | succ k ih =>
      intro i hi x hx
      by_cases hlow : nabs F (x i.castSucc) < threshold r R (nabs F c) (k + 1)
      · have hk : k < n := by omega
        have hi' : (⟨k, hk⟩ : Fin n).succ = i.castSucc := Fin.ext (by simp [hi])
        exact ih ⟨k, hk⟩ rfl x (by rw [hi']; exact hlow)
      · exact sliceIntegral_eq_zero_step ψ hr hconst hsupp hc hc0 i (hθ (k + 1)) x
          (Or.inr (not_lt.1 hlow)) hx
  intro b hb x hx
  have hb' : (b.pred hb).succ = b := Fin.succ_pred b hb
  refine main (b.pred hb).val (b.pred hb) rfl x ?_
  rw [hb']
  have hv : (b.pred hb).val + 1 = b.val := by
    rw [Fin.val_pred]
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    omega
  rw [hv]
  exact hx

/-- A nontrivial additive character differs from one at some nonzero point. -/
theorem exists_character_ne_one (ψ : UnitaryAdditiveCharacter F) :
    ∃ c : F, ψ.complex c ≠ 1 ∧ c ≠ 0 := by
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.1 ψ.nontrivial
  have hψc : ψ.complex c ≠ 1 := by
    intro h
    apply hc
    apply Circle.ext
    rw [Circle.coe_one]
    exact h
  refine ⟨c, hψc, ?_⟩
  rintro rfl
  exact hψc (AddChar.map_zero_eq_one _)

/-- The slice integral of a compactly supported locally constant function is
locally constant. -/
theorem sliceIntegral_isLocallyConstant (ψ : UnitaryAdditiveCharacter F)
    {f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsLocallyConstant (sliceIntegral F ψ f) := by
  obtain ⟨r, hr, hconst⟩ := exists_uniform_constancy f hf hc
  obtain ⟨R, hsupp⟩ := exists_support_bound f hc
  obtain ⟨c, hψc, hc0⟩ := exists_character_ne_one ψ
  set θ : Fin (n + 1) → ℝ := fun b => threshold r R (nabs F c) b.val with hθdef
  have hθ : ∀ b, 0 < θ b := fun b => threshold_pos hr (nabs_pos hc0) b.val
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hgood : ∀ b, b = 0 ∨ θ b ≤ nabs F (x b)
  · set M : Fin (n + 1) → ℝ := fun b => max 1 (R / θ b) with hMdef
    have hM : ∀ b, 0 < M b := fun b => one_pos.trans_le (le_max_left _ _)
    set ρ : Fin (n + 1) → ℝ := fun b => min (θ b) (r / M b) with hρdef
    have hρ : ∀ b, 0 < ρ b := fun b => lt_min (hθ b) (div_pos hr (hM b))
    have hnear : ∀ᶠ x' in 𝓝 x, ∀ b, nabs F (x' b - x b) < ρ b := by
      refine Filter.eventually_all.2 fun b => ?_
      have hcont : Continuous fun x' : Fin (n + 1) → F => nabs F (x' b - x b) :=
        continuous_nabs.comp ((continuous_apply b).sub continuous_const)
      exact (hcont.tendsto x).eventually_lt_const (by rw [sub_self, nabs_zero]; exact hρ b)
    filter_upwards [hnear] with x' hx'
    have hgood' : ∀ b, b = 0 ∨ θ b ≤ nabs F (x' b) := by
      intro b
      rcases hgood b with h | h
      · exact Or.inl h
      · refine Or.inr (h.trans ?_)
        have e := nabs_add_le_max (x' b) (x b - x' b)
        rw [add_sub_cancel] at e
        have hd : nabs F (x b - x' b) < nabs F (x b) := by
          rw [← nabs_neg, neg_sub]
          exact (hx' b).trans_le ((min_le_left _ _).trans h)
        rcases le_max_iff.1 e with h1 | h1
        · exact h1
        · exact absurd h1 (not_le.2 hd)
    unfold sliceIntegral
    congr 1
    funext u
    congr 1
    apply eq_of_small_diff hconst
    intro hnz a b
    rw [Matrix.mul_diagonal, Matrix.mul_diagonal, ← mul_sub, nabs_mul]
    have hu : nabs F (u.val a b) ≤ M b := by
      rcases hnz with h | h
      · exact column_bound (hθ b) (hgood b) (fun a' => by
          have e := hsupp _ h a' b
          rwa [Matrix.mul_diagonal] at e) a
      · exact column_bound (hθ b) (hgood' b) (fun a' => by
          have e := hsupp _ h a' b
          rwa [Matrix.mul_diagonal] at e) a
    calc nabs F (u.val a b) * nabs F (x' b - x b) ≤ M b * nabs F (x' b - x b) :=
          mul_le_mul_of_nonneg_right hu (nabs_nonneg _)
      _ < r := (lt_div_iff₀' (hM b)).1 ((hx' b).trans_le (min_le_right _ _))
  · push Not at hgood
    obtain ⟨b, hb0, hbx⟩ := hgood
    have hcont : Continuous fun x' : Fin (n + 1) → F => nabs F (x' b) :=
      continuous_nabs.comp (continuous_apply b)
    filter_upwards [(hcont.tendsto x).eventually_lt_const hbx] with x' hx'
    rw [sliceIntegral_eq_zero_of_lt_threshold ψ hr hconst hsupp hψc hc0 b hb0 x' hx',
      sliceIntegral_eq_zero_of_lt_threshold ψ hr hconst hsupp hψc hc0 b hb0 x hbx]

/-- The slice integral of a compactly supported function has compact support:
it vanishes unless every `x_j` is a diagonal entry of a matrix in the support. -/
theorem sliceIntegral_hasCompactSupport (ψ : UnitaryAdditiveCharacter F)
    {f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (sliceIntegral F ψ f) := by
  have := localField_t2 F
  refine HasCompactSupport.intro
    (K := Set.univ.pi fun j =>
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M j j) '' tsupport f)
    (isCompact_univ_pi fun j => hc.isCompact.image (continuous_id.matrix_elem j j)) ?_
  intro x hx
  simp only [Set.mem_univ_pi, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  have h0 : ∀ u : upperUnipotent (n + 1) F,
      f (u.val.val * Matrix.diagonal x) = 0 := by
    intro u
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hj
    refine ⟨_, hmem, ?_⟩
    show (u.val.val * Matrix.diagonal x) j j = x j
    rw [Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul]
  simp only [sliceIntegral, h0, zero_mul, integral_zero]

/-- The slice integral of a Schwartz–Bruhat function on square matrices is
Schwartz–Bruhat on `F^(n+1)`. -/
theorem sliceIntegral_mem (ψ : UnitaryAdditiveCharacter F)
    {f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ}
    (hf : f ∈ schwartzBruhatSubmodule (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    sliceIntegral F ψ f ∈ schwartzBruhatSubmodule (Fin (n + 1) → F) :=
  ⟨sliceIntegral_isLocallyConstant ψ hf.1 hf.2, sliceIntegral_hasCompactSupport ψ hf.2⟩

/-- Right multiplication by an invertible matrix, as a homeomorphism of all
square matrices. -/
def rightMulHomeomorph (k : Langlands.GeneralLinear (n + 1) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F ≃ₜ
      Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun M := M * k.val
  invFun M := M * k⁻¹.val
  left_inv M := by
    change M * k.val * k⁻¹.val = M
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv M := by
    change M * k⁻¹.val * k.val = M
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

/-- The slice integral of a right translate `M ↦ Φ(M k)` of a matrix test
function is Schwartz–Bruhat on `F^(n+1)`. -/
theorem sliceIntegral_rightTranslate_mem (ψ : UnitaryAdditiveCharacter F)
    (Φ : MatrixTestFunction n F) (k : Langlands.GeneralLinear (n + 1) F) :
    sliceIntegral F ψ (fun M => Φ (M * k.val)) ∈
      schwartzBruhatSubmodule (Fin (n + 1) → F) :=
  sliceIntegral_mem ψ ⟨Φ.2.1.comp_continuous (rightMulHomeomorph k).continuous,
    Φ.2.2.comp_homeomorph (rightMulHomeomorph k)⟩

end Slice

end Langlands.AllField.GodementJacquet.WhittakerSlice
