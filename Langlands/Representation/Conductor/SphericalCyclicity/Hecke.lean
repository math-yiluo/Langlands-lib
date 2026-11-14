import Langlands.Representation.Conductor.SphericalCyclicity.Weyl
import Langlands.Representation.Conductor.SphericalCyclicity.Counting

/-!
# The Hecke operator of the parahoric subgroup and the extension of the spherical section

For a residue-class tuple `c : Fin (n + 1) → 𝓀` let `s(c)` be a chosen integral lift and
`g_c = t' L(s(c))`, where `t' = diag(1, ϖ, …, ϖ)` and `L(y)` is the lower unipotent matrix
with first-column tail `y`. The operator `T' f = Σ_c ρ(g_c) f` preserves every
subrepresentation and the parahoric-invariant vectors, and on the values at the Weyl
representatives `w_j` it acts by a nonzero multiple of `cellMatrix`.

Combined with the linear-algebra lemma `eq_top_of_cellMatrix_stable`, this shows that a
subrepresentation containing the spherical section contains the extension by zero of the
spherical section of the smaller principal series (`extend_sphericalSection_mem`).
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.Induction
open scoped BigOperators

universe uF

/-! ### A reindexing lemma for finite sums of translates -/

/-- If right multiplication by `k` permutes the cosets `g c H`, then summing a right
`H`-invariant function over the translates `x k g c` or over `x g c` gives the same result. -/
theorem sum_mul_reindex {G ι : Type*} [Group G] [Fintype ι] (H : Subgroup G) (g : ι → G)
    (φ : G → ℂ) (hφ : ∀ h ∈ H, ∀ x, φ (x * h) = φ x) (k : G)
    (hk : ∀ c, ∃ c', (g c')⁻¹ * k * g c ∈ H)
    (hinj : ∀ c₁ c₂, (g c₁)⁻¹ * g c₂ ∈ H → c₁ = c₂) (x : G) :
    ∑ c, φ (x * k * g c) = ∑ c, φ (x * g c) := by
  choose σ hσ using hk
  have hσinj : Function.Injective σ := by
    intro c₁ c₂ h
    apply hinj
    have h1 := hσ c₁
    have h2 := hσ c₂
    rw [h] at h1
    have hm := mul_mem (inv_mem h1) h2
    have e : ((g (σ c₂))⁻¹ * k * g c₁)⁻¹ * ((g (σ c₂))⁻¹ * k * g c₂) = (g c₁)⁻¹ * g c₂ := by
      group
    rwa [e] at hm
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hσinj
  have hterm : ∀ c, φ (x * k * g c) = φ (x * g (σ c)) := by
    intro c
    have e : x * k * g c = x * g (σ c) * ((g (σ c))⁻¹ * k * g c) := by group
    rw [e, hφ _ (hσ c)]
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  exact (Equiv.ofBijective σ hbij).sum_comp (fun c => φ (x * g c))

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer
set_option quotPrecheck false in
local notation "𝓀" => IsLocalRing.ResidueField (ValuativeRel.valuation F).integer

variable {n : ℕ}

/-! ### Lifts of residue classes -/

/-- A chosen integral lift of each residue class. -/
def resLift : 𝓀 → 𝒪 := Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪))

theorem residue_resLift (c : 𝓀) : IsLocalRing.residue 𝒪 (resLift c) = c :=
  Function.surjInv_eq _ c

/-- The coordinatewise lift of a residue-class tuple. -/
def liftVec {m : ℕ} (c : Fin m → 𝓀) : Fin m → F := fun i => ((resLift (c i) : 𝒪) : F)

theorem liftVec_mem {m : ℕ} (c : Fin m → 𝓀) (i : Fin m) : liftVec c i ∈ 𝒪 :=
  (resLift (c i)).property

theorem lowerUnip_mem_integral {y : Fin (n + 1) → F} (hy : ∀ i, y i ∈ 𝒪) :
    lowerUnip y ∈ integralSubgroup 𝒪 (n + 1) := by
  apply Unramified.MinusculeCosets.mem_integralSubgroup_of_det
  · intro i j
    rw [lowerUnip_val]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
    · simpa using hy i
    · simp only [blk_succ_succ]
      by_cases h : i = j
      · rw [h, Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne h]; exact zero_mem _
  · rw [det_lowerUnip, map_one]

/-! ### The first column of `w_j L(y)` -/

omit [ValuativeRel F] in
theorem weyl_mul_lowerUnip_self (j : Fin (n + 2)) (y : Fin (n + 1) → F) :
    (weyl j * lowerUnip y : GL (Fin (n + 2)) F).val j 0 = 1 := by
  rw [Units.val_mul, weyl_mul_val]
  change (lowerUnip y).val (Equiv.swap 0 j j) 0 = 1
  rw [Equiv.swap_apply_right]
  rfl

omit [ValuativeRel F] in
theorem weyl_mul_lowerUnip_succ (j : Fin (n + 2)) (y : Fin (n + 1) → F) (i : Fin (n + 1))
    (h : i.succ ≠ j) : (weyl j * lowerUnip y : GL (Fin (n + 2)) F).val i.succ 0 = y i := by
  rw [Units.val_mul, weyl_mul_val]
  change (lowerUnip y).val (Equiv.swap 0 j i.succ) 0 = y i
  rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) h]
  rfl

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

include hϖ in
theorem residue_eq_zero_iff_val (x : 𝒪) :
    IsLocalRing.residue 𝒪 x = 0 ↔ 𝒱 (x : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, ← pow_one (IsLocalRing.maximalIdeal 𝒪),
    mem_maximalIdeal_pow_iff hϖ 1 x, pow_one, val_lt_one_iff_le_uniformizer hϖ]

include hϖ in
theorem residue_eq_iff (x y : 𝒪) :
    IsLocalRing.residue 𝒪 x = IsLocalRing.residue 𝒪 y ↔ 𝒱 ((x : F) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val hϖ]
  rfl

include hϖ in
theorem val_liftVec_lt_one_iff {m : ℕ} (c : Fin m → 𝓀) (i : Fin m) :
    𝒱 (liftVec c i) < 1 ↔ c i = 0 := by
  rw [← residue_resLift (c i), residue_eq_zero_iff_val hϖ]
  rfl

include hϖ in
theorem val_liftVec_eq_one {m : ℕ} (c : Fin m → 𝓀) {i : Fin m} (h : c i ≠ 0) :
    𝒱 (liftVec c i) = 1 :=
  le_antisymm (val_le_one_of_mem (liftVec_mem c i))
    (not_lt.1 fun hlt => h ((val_liftVec_lt_one_iff hϖ c i).1 hlt))

/-! ### The Hecke translates `g_c = t' L(s(c))` -/

/-- The translate `t' L(s(c))`. -/
def heckeElt (ϖ : Fˣ) (c : Fin (n + 1) → 𝓀) : GL (Fin (n + 2)) F :=
  tPrime ϖ * lowerUnip (liftVec c)

include hϖ in
theorem conj_mem_integral_of_parahoric {x : GL (Fin (n + 2)) F} (hx : x ∈ parahoric ϖ) :
    (tPrime ϖ)⁻¹ * x * tPrime ϖ ∈ integralSubgroup 𝒪 (n + 1) := by
  obtain ⟨hK, hc⟩ := (mem_parahoric_iff hϖ x).1 hx
  exact (integral_tPrime_conj_iff hϖ x hK).2 hc

theorem tPrime_mul_lowerUnip (y : Fin (n + 1) → F) :
    tPrime ϖ * lowerUnip y = lowerUnip ((ϖ : F) • y) * (tPrime ϖ : GL (Fin (n + 2)) F) := by
  have h := tPrime_inv_lowerUnip_tPrime (ϖ := ϖ) ((ϖ : F) • y)
  rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero ϖ), one_smul] at h
  rw [← h]
  group

include hϖ in
theorem heckeElt_inj (c₁ c₂ : Fin (n + 1) → 𝓀)
    (h : (heckeElt ϖ c₁)⁻¹ * heckeElt ϖ c₂ ∈ parahoric ϖ) : c₁ = c₂ := by
  have e : (heckeElt ϖ c₁)⁻¹ * heckeElt ϖ c₂ = lowerUnip (liftVec c₂ - liftVec c₁) := by
    rw [heckeElt, heckeElt, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, lowerUnip_inv,
      lowerUnip_add, neg_add_eq_sub]
  rw [e, mem_parahoric_iff hϖ] at h
  funext i
  have hi := h.2 i
  rw [colT_lowerUnip, Pi.sub_apply] at hi
  have := (residue_eq_iff hϖ (resLift (c₂ i)) (resLift (c₁ i))).2 hi
  rw [residue_resLift, residue_resLift] at this
  exact this.symm

include hϖ in
theorem heckeElt_perm {k : GL (Fin (n + 2)) F} (hk : k ∈ parahoric ϖ) (c : Fin (n + 1) → 𝓀) :
    ∃ c', (heckeElt ϖ c')⁻¹ * k * heckeElt ϖ c ∈ parahoric ϖ := by
  set y := liftVec c with hy
  set k' := k * lowerUnip ((ϖ : F) • y) with hk'
  have hsmall : ∀ i, 𝒱 (((ϖ : F) • y) i) < 1 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul]
    exact val_mul_lt_one (val_le_one_of_mem (liftVec_mem c i)) hϖ.1 |>.trans_eq' (by
      rw [mul_comm])
  have hk'J : k' ∈ parahoric ϖ := mul_mem hk (lowerUnip_mem_parahoric hϖ hsmall)
  set Y := (tPrime ϖ)⁻¹ * k' * tPrime ϖ with hY
  have hYK : Y ∈ integralSubgroup 𝒪 (n + 1) := conj_mem_integral_of_parahoric hϖ hk'J
  have hY00 : 𝒱 (Y.val 0 0) = 1 := by
    rw [hY, tPrime_conj_val, blk_zero_zero]
    exact (parahoric_head hϖ hk'J).1
  have hY0 : Y.val 0 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hY00
    exact zero_ne_one hY00
  have hYeq : k * heckeElt ϖ c = tPrime ϖ * Y := by
    rw [hY, heckeElt, hk', tPrime_mul_lowerUnip]
    group
    rfl
  set u : Fin (n + 1) → F := fun i => colT Y.val i / Y.val 0 0 with hu
  have hu_mem : ∀ i, u i ∈ 𝒪 := by
    intro i
    apply mem_of_val_le_one
    rw [hu, map_div₀, hY00, div_one]
    exact val_le_one_of_mem (integral_entry hYK _ _)
  refine ⟨fun i => IsLocalRing.residue 𝒪 ⟨u i, hu_mem i⟩, ?_⟩
  set y' := liftVec (fun i => IsLocalRing.residue 𝒪 ⟨u i, hu_mem i⟩) with hy'
  have e : (heckeElt ϖ (fun i => IsLocalRing.residue 𝒪 ⟨u i, hu_mem i⟩))⁻¹ * k *
      heckeElt ϖ c = lowerUnip (-y') * Y := by
    rw [mul_assoc, hYeq, heckeElt, _root_.mul_inv_rev, ← hy', lowerUnip_inv]
    group
  rw [e, mem_parahoric_iff hϖ]
  refine ⟨mul_mem (lowerUnip_mem_integral fun i => neg_mem (liftVec_mem _ i)) hYK, fun i => ?_⟩
  rw [Units.val_mul, colT_mul, colT_lowerUnip, low_lowerUnip, one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  have hcol : colT Y.val i = Y.val 0 0 * u i := by
    rw [hu]
    field_simp
  have hres := (residue_eq_iff hϖ (resLift (IsLocalRing.residue 𝒪 ⟨u i, hu_mem i⟩))
    ⟨u i, hu_mem i⟩).1 (residue_resLift _)
  have e2 : Y.val 0 0 * -y' i + colT Y.val i = -(Y.val 0 0 * (y' i - u i)) := by
    rw [hcol]
    ring
  rw [e2, Valuation.map_neg, map_mul, hY00, one_mul]
  exact hres

/-! ### The Hecke operator -/

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

noncomputable local instance : Fintype 𝓀 := Fintype.ofFinite _

open Classical

variable {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}

theorem card_residue (hq : IsResidueCardinality (F := F) q) : Fintype.card 𝓀 = q := by
  rw [hq, Nat.card_eq_fintype_card]

/-- The Hecke operator `T' f = Σ_c ρ(t' L(s(c))) f`. -/
def hecke (f : PrincipalSeries hϖ (n + 1) hq z) : PrincipalSeries hϖ (n + 1) hq z :=
  ∑ c : Fin (n + 1) → 𝓀, principalSeries hϖ (n + 1) hq z (heckeElt ϖ c) f

theorem value_hecke (f : PrincipalSeries hϖ (n + 1) hq z) (x : GL (Fin (n + 2)) F) :
    value hϖ (n + 1) (hecke hϖ f) x =
      ∑ c : Fin (n + 1) → 𝓀, value hϖ (n + 1) f (x * heckeElt ϖ c) := by
  rw [hecke, value_sum]
  rfl

theorem hecke_mem (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    {f : PrincipalSeries hϖ (n + 1) hq z} (hf : f ∈ S) : hecke hϖ f ∈ S :=
  S.toSubmodule.sum_mem fun c _ => S.apply_mem_toSubmodule _ hf

theorem hecke_parahoricInvariant {f : PrincipalSeries hϖ (n + 1) hq z}
    (hf : IsParahoricInvariant hϖ f) : IsParahoricInvariant hϖ (hecke hϖ f) := by
  intro k hk x
  rw [value_hecke, value_hecke]
  exact sum_mul_reindex (parahoric ϖ) (heckeElt ϖ) (value hϖ (n + 1) f)
    (fun h hh x => hf h hh x) k (heckeElt_perm hϖ hk) (heckeElt_inj hϖ) x

/-- The cell lemma at `w_j L(s(c))`: the relevant Weyl representative is `w_{max(j, top c)}`. -/
theorem value_weyl_mul_lowerUnip {f : PrincipalSeries hϖ (n + 1) hq z}
    (hf : IsParahoricInvariant hϖ f) (j : Fin (n + 2)) (c : Fin (n + 1) → 𝓀) :
    value hϖ (n + 1) f (weyl j * lowerUnip (liftVec c)) =
      value hϖ (n + 1) f (weyl (cellIndex j c)) := by
  apply value_eq_weyl hϖ hf
    (mul_mem (weyl_mem_integral j) (lowerUnip_mem_integral (liftVec_mem c)))
  · by_cases h : top c ≤ (j : ℕ)
    · have e : cellIndex j c = j := Fin.ext (by rw [cellIndex_val]; exact max_eq_left h)
      rw [e, weyl_mul_lowerUnip_self, map_one]
    · push_neg at h
      have hval : (cellIndex j c : ℕ) = top c := by
        rw [cellIndex_val]
        exact max_eq_right h.le
      have hne0 : cellIndex j c ≠ 0 := by
        intro h0
        rw [h0, Fin.val_zero] at hval
        omega
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 hne0
      have hv : ((i.succ : Fin (n + 2)) : ℕ) = top c := by rw [hi, hval]
      have hij : i.succ ≠ j := by
        intro e
        rw [e] at hv
        omega
      rw [← hi, weyl_mul_lowerUnip_succ _ _ _ hij]
      exact val_liftVec_eq_one hϖ c (ne_zero_of_top_eq c i (by rw [← hv, Fin.val_succ]))
  · intro r hr
    have hr0 : r ≠ 0 := (lt_of_le_of_lt (Fin.zero_le _) hr).ne'
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hr0
    have hlt : max (j : ℕ) (top c) < (i : ℕ) + 1 := by
      rw [← cellIndex_val, ← Fin.val_succ]
      exact hr
    have h1 := le_max_left (j : ℕ) (top c)
    have h2 := le_max_right (j : ℕ) (top c)
    have hij : i.succ ≠ j := by
      intro e
      have hj' := lt_of_le_of_lt h1 hlt
      rw [← e, Fin.val_succ] at hj'
      omega
    rw [weyl_mul_lowerUnip_succ _ _ _ hij]
    exact (val_liftVec_lt_one_iff hϖ c i).2 (eq_zero_of_top_le c i (by omega))

/-- Evaluation at the Weyl representatives `w_j`. -/
def weylEval (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ) :
    PrincipalSeries hϖ (n + 1) hq z →ₗ[ℂ] (Fin (n + 2) → ℂ) :=
  LinearMap.pi fun j => evalAt hϖ hq z (weyl j)

theorem weylEval_apply (f : PrincipalSeries hϖ (n + 1) hq z) (j : Fin (n + 2)) :
    weylEval hϖ hq z f j = value hϖ (n + 1) f (weyl j) := rfl

/-- The constant `√q^(n+1) Π z_i` by which `T'` acts through `cellMatrix`. -/
def heckeConst (q : ℕ) (z : Fin (n + 2) → ℂˣ) : ℂ :=
  ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^ (n + 1) * ∏ i, (z i : ℂ)

theorem heckeConst_ne_zero (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ) :
    heckeConst q z ≠ 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast residueCardinality_pos hq
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq0).ne'))
    (Finset.prod_ne_zero_iff.2 fun i _ => (z i).ne_zero)

/-- On the values at the `w_j`, the Hecke operator acts by `heckeConst • cellMatrix`. -/
theorem weylEval_hecke {f : PrincipalSeries hϖ (n + 1) hq z} (hf : IsParahoricInvariant hϖ f)
    (j : Fin (n + 2)) :
    weylEval hϖ hq z (hecke hϖ f) j =
      heckeConst q z * (cellMatrix (n + 2) q (fun i => (z i : ℂ)) *ᵥ weylEval hϖ hq z f) j := by
  set χ : ℂ := (normalizedCharacter hϖ (n + 1) hq z (torusBorel (n + 1) ϖ (lamJ j)) : ℂ)
    with hχ
  have hstep : ∀ c, value hϖ (n + 1) f (weyl j * heckeElt ϖ c) =
      χ * weylEval hϖ hq z f (cellIndex j c) := by
    intro c
    have e : weyl j * heckeElt ϖ c =
        (torusBorel (n + 1) ϖ (lamJ j)).val * (weyl j * lowerUnip (liftVec c)) := by
      rw [heckeElt, ← mul_assoc, weyl_mul_tPrime, mul_assoc]
      rfl
    rw [e, value_borel_mul, value_weyl_mul_lowerUnip hϖ hf, weylEval_apply]
  rw [weylEval_apply, value_hecke, Finset.sum_congr rfl (fun c _ => hstep c), ← Finset.mul_sum,
    sum_cellIndex (card_residue hq) (fun i => (z i : ℂ)) (fun i => (z i).ne_zero), ← mul_assoc,
    hχ, normalizedCharacter_lamJ hϖ hq z j]
  rfl

/-! ### The extension of the spherical section -/

/-- The parahoric-invariant vectors. -/
def parahoricInvariants (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ) :
    Submodule ℂ (PrincipalSeries hϖ (n + 1) hq z) where
  carrier := {f | IsParahoricInvariant hϖ f}
  add_mem' := by
    intro f g hf hg k hk x
    rw [value_add, value_add, hf k hk x, hg k hk x]
  zero_mem' := by
    intro k hk x
    rw [value_zero, value_zero]
  smul_mem' := by
    intro c f hf k hk x
    rw [value_smul, value_smul, hf k hk x]

theorem sphericalSection_parahoricInvariant :
    IsParahoricInvariant hϖ (sphericalSection hϖ (n + 1) hq z) := by
  intro k hk x
  exact sphericalSection_mul_integral hϖ (n + 1) hq z x ((mem_parahoric_iff hϖ k).1 hk).1

theorem extend_sphericalSection_parahoricInvariant :
    IsParahoricInvariant hϖ (extend hϖ hq z (sphericalSection hϖ n hq (tailParam z))) := by
  intro k hk x
  rw [extend_value, extend_value, extFun, extFun, cellFun_mul_parahoric hϖ hq z _ x hk,
    cellFun_isSmall]
  split_ifs with hx
  · rw [sphericalSection_mul_integral hϖ n hq (tailParam z) _
      (lowGL_mem_integral_of_parahoric hϖ (cell_mul_parahoric hϖ hx hk).2.1)]
  · rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem not_isUnit_det_low_weyl {j : Fin (n + 2)} (hj : j ≠ 0) :
    ¬IsUnit (low (weyl j : GL (Fin (n + 2)) F).val).det := by
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
  have hrow : ∀ l, low (weyl i.succ : GL (Fin (n + 2)) F).val i l = 0 := by
    intro l
    rw [low_apply, weyl_apply, Equiv.swap_apply_right, Pi.single_apply, if_neg (Fin.succ_ne_zero l)]
  rw [Matrix.det_eq_zero_of_row_eq_zero i hrow]
  exact not_isUnit_zero

theorem weylEval_extend_sphericalSection :
    weylEval hϖ hq z (extend hϖ hq z (sphericalSection hϖ n hq (tailParam z))) =
      Pi.single 0 1 := by
  funext j
  rw [weylEval_apply, extend_value, extFun, cellFun_isSmall]
  by_cases hj : j = 0
  · subst hj
    have h1 : (1 : GL (Fin (n + 2)) F) ∈ parahoric ϖ := one_mem _
    have hK' := lowGL_mem_integral_of_parahoric hϖ h1
    rw [weyl_zero, if_pos (inCell_of_parahoric hϖ h1), Pi.single_eq_same,
      sphericalSection_integral hϖ n hq (tailParam z) hK', mul_one, cellScalar, headOrd,
      ordDet_one, ordDet_eq_zero_of_integral hϖ hK']
    simp
  · rw [if_neg (fun h => not_isUnit_det_low_weyl hj h.1), Pi.single_eq_of_ne hj]

/-- **Step A.** A subrepresentation containing the spherical section contains the extension
by zero of the spherical section of the smaller principal series. -/
theorem extend_sphericalSection_mem (hmono : Monotone fun i => ‖(z i : ℂ)‖)
    (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    (hS : sphericalSection hϖ (n + 1) hq z ∈ S) :
    extend hϖ hq z (sphericalSection hϖ n hq (tailParam z)) ∈ S := by
  set V := S.toSubmodule ⊓ parahoricInvariants hϖ hq z with hV
  set W := V.map (weylEval hϖ hq z) with hW
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Finite.one_lt_card
  have hone : (fun _ => (1 : ℂ)) ∈ W := by
    refine ⟨sphericalSection hϖ (n + 1) hq z,
      Submodule.mem_inf.2 ⟨hS, sphericalSection_parahoricInvariant hϖ⟩, ?_⟩
    funext j
    rw [weylEval_apply]
    exact sphericalSection_integral hϖ (n + 1) hq z (weyl_mem_integral j)
  have hA : ∀ v ∈ W, (cellMatrix (n + 2) q (fun i => (z i : ℂ))).mulVec v ∈ W := by
    rintro v ⟨f, hfV, rfl⟩
    obtain ⟨hfS, hfJ⟩ := Submodule.mem_inf.1 hfV
    refine ⟨(heckeConst q z)⁻¹ • hecke hϖ f, Submodule.mem_inf.2
      ⟨S.toSubmodule.smul_mem _ (hecke_mem hϖ S hfS),
        (parahoricInvariants hϖ hq z).smul_mem _ (hecke_parahoricInvariant hϖ hfJ)⟩, ?_⟩
    funext j
    rw [map_smul, Pi.smul_apply, weylEval_hecke hϖ hfJ j, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (heckeConst_ne_zero hq z), one_mul]
  have htop := eq_top_of_cellMatrix_stable hq2 (fun i => (z i : ℂ)) (fun i => (z i).ne_zero)
    hmono W hone hA
  have hmem : (Pi.single 0 1 : Fin (n + 2) → ℂ) ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨f, hfV, hfe⟩ := hmem
  obtain ⟨hfS, hfJ⟩ := Submodule.mem_inf.1 hfV
  have heq : f = extend hϖ hq z (sphericalSection hϖ n hq (tailParam z)) := by
    apply eq_of_weyl hϖ hfJ (extend_sphericalSection_parahoricInvariant hϖ)
    intro j
    rw [← weylEval_apply, ← weylEval_apply, hfe, weylEval_extend_sphericalSection hϖ]
  rw [← heq]
  exact hfS

end Langlands.Conductor.SphericalCyclicity
