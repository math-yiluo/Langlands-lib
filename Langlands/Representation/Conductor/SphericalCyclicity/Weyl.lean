import Langlands.Representation.Conductor.SphericalCyclicity.Cellular

/-!
# Weyl representatives for the parahoric cells

For `j : Fin (n + 2)` let `w j` be the permutation matrix of the transposition `(0 j)`.
This file proves:

* `w j * t' = τ_j * w j`, where `t' = diag(1, ϖ, …, ϖ)` and `τ_j` is the diagonal
  matrix with `1` at `j` and `ϖ` elsewhere, together with the value of the normalized
  character at `τ_j`;
* the cell lemma: a function in the principal series that is right invariant under the
  parahoric subgroup `J` takes at an integral matrix `κ` the value it takes at `w m`,
  where `m` is the last row in which the first column of `κ` has a unit entry;
* consequently such a function is determined by its values at the `w j`.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.Induction
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

variable {n : ℕ}

/-! ### The transpositions `(0 j)` -/

/-- The permutation matrix of the transposition `(0 j)`. -/
def weyl (j : Fin (n + 2)) : GL (Fin (n + 2)) F where
  val := (Equiv.swap 0 j).permMatrix F
  inv := (Equiv.swap 0 j).permMatrix F
  val_inv := by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]

omit [ValuativeRel F] in
theorem weyl_val (j : Fin (n + 2)) :
    ((weyl j : GL (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) =
      (Equiv.swap 0 j).permMatrix F := rfl

omit [ValuativeRel F] in
theorem weyl_apply (j r l : Fin (n + 2)) :
    ((weyl j : GL (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) r l =
      (Pi.single (Equiv.swap 0 j r) (1 : F) : Fin (n + 2) → F) l :=
  congrFun (PEquiv.toMatrix_toPEquiv_apply _ r) l

omit [ValuativeRel F] in
theorem weyl_mul_val (j : Fin (n + 2)) (M : Matrix (Fin (n + 2)) (Fin (n + 2)) F) :
    ((weyl j : GL (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) * M =
      M.submatrix (Equiv.swap 0 j) id :=
  PEquiv.toMatrix_toPEquiv_mul _ _

omit [ValuativeRel F] in
theorem weyl_mul_self (j : Fin (n + 2)) : weyl j * weyl j = (1 : GL (Fin (n + 2)) F) :=
  Units.ext (weyl j).val_inv

omit [ValuativeRel F] in
theorem weyl_zero : weyl 0 = (1 : GL (Fin (n + 2)) F) := by
  apply Units.ext
  rw [weyl_val, Equiv.swap_self, permMatrix_refl, Units.val_one]

theorem weyl_mem_integral (j : Fin (n + 2)) :
    (weyl j : GL (Fin (n + 2)) F) ∈ integralSubgroup 𝒪 (n + 1) := by
  have h : ∀ r l : Fin (n + 2),
      ((weyl j : GL (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) r l ∈ 𝒪 := by
    intro r l
    rw [weyl_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hinv : (weyl j)⁻¹ = (weyl j : GL (Fin (n + 2)) F) := by
    rw [inv_eq_iff_mul_eq_one, weyl_mul_self]
  refine (mem_integralSubgroup 𝒪 (n + 1) _).2 ⟨h, ?_⟩
  rw [hinv]
  exact h

/-! ### The torus relation -/

omit [ValuativeRel F] in
theorem tPrime_val_eq (ϖ : Fˣ) :
    ((tPrime ϖ : GL (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) =
      diagonal (fun i : Fin (n + 2) => if i = 0 then (1 : F) else (ϖ : F)) := by
  rw [tPrime, blockDiag_val]
  ext r l
  refine Fin.cases ?_ (fun r => ?_) r <;> refine Fin.cases ?_ (fun l => ?_) l
  · simp
  · simp [diagonal_apply, (Fin.succ_ne_zero l).symm]
  · simp [diagonal_apply, Fin.succ_ne_zero r]
  · simp [diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Fin.succ_inj]

/-- The exponent vector with `0` at `j` and `1` elsewhere. -/
def lamJ (j i : Fin (n + 2)) : ℤ := if i = j then 0 else 1

theorem lamJ_self (j : Fin (n + 2)) : lamJ j j = 0 := if_pos rfl

theorem lamJ_of_ne {j i : Fin (n + 2)} (h : i ≠ j) : lamJ j i = 1 := if_neg h

omit [ValuativeRel F] in
/-- `w j * t' = τ_j * w j`. -/
theorem weyl_mul_tPrime (ϖ : Fˣ) (j : Fin (n + 2)) :
    weyl j * tPrime ϖ = Iwasawa.torus ϖ (lamJ j) * (weyl j : GL (Fin (n + 2)) F) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, weyl_mul_val, tPrime_val_eq, Iwasawa.torus_val, weyl_val,
    PEquiv.mul_toMatrix_toPEquiv]
  ext r l
  simp only [submatrix_apply, id, diagonal_apply, Equiv.symm_swap]
  by_cases h : Equiv.swap 0 j r = l
  · have h' : r = Equiv.swap 0 j l := Equiv.swap_apply_eq_iff.1 h
    rw [if_pos h, if_pos h']
    by_cases hr : r = j
    · rw [hr, Equiv.swap_apply_right, if_pos rfl, lamJ_self, zpow_zero, Units.val_one]
    · have hs : Equiv.swap 0 j r ≠ 0 := by
        intro h0
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
        exact hr h0
      rw [if_neg hs, lamJ_of_ne hr, zpow_one]
  · have h' : ¬r = Equiv.swap 0 j l := fun h' => h (Equiv.swap_apply_eq_iff.2 h')
    rw [if_neg h, if_neg h']

/-! ### The value of the normalized character on `τ_j` -/

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

theorem normalizedCharacter_torusBorel {m q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (m + 1) → ℂˣ) (lam : Fin (m + 1) → ℤ) :
    (normalizedCharacter hϖ m hq z (torusBorel m ϖ lam) : ℂ) =
      Spherical.halfModulus q lam * ∏ i, (z i : ℂ) ^ lam i := by
  have h1 := sphericalSection_torus hϖ m hq z lam
  have h2 := sphericalSection_borel_mul_integral hϖ m hq z (torusBorel m ϖ lam)
    (one_mem (integralSubgroup (ValuativeRel.valuation F).integer m))
  rw [mul_one, torusBorel_val] at h2
  rw [← h2, h1]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem sum_weight_eq_zero :
    ∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) = 0 := by
  have h := Finset.sum_range_id_mul_two (n + 2)
  rw [show n + 2 - 1 = n + 1 by omega] at h
  have h' : (∑ i ∈ Finset.range (n + 2), (i : ℤ)) * 2 = ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    linarith
  rw [Fin.sum_univ_eq_sum_range (fun i => (((n + 1 : ℕ) : ℤ) - 2 * (i : ℤ))) (n + 2),
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    nsmul_eq_mul]
  push_cast
  linear_combination -h'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem weight_lamJ (j : Fin (n + 2)) :
    -∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) * lamJ j i =
      (n : ℤ) + 1 - 2 * ((j : ℕ) : ℤ) := by
  have hlam : ∀ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) * lamJ j i =
      (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) -
        if i = j then (((n + 1 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ)) else 0 := by
    intro i
    by_cases h : i = j
    · rw [h, lamJ_self, if_pos rfl]
      ring
    · rw [lamJ_of_ne h, if_neg h]
      ring
  rw [Finset.sum_congr rfl (fun i _ => hlam i), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), sum_weight_eq_zero]
  push_cast
  ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem prod_lamJ (z : Fin (n + 2) → ℂˣ) (j : Fin (n + 2)) :
    (∏ i, (z i : ℂ) ^ lamJ j i) * (z j : ℂ) = ∏ i, (z i : ℂ) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (z i : ℂ) ^ lamJ j i) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => (z i : ℂ)) (Finset.mem_univ j)]
  have he : ∏ i ∈ Finset.univ.erase j, (z i : ℂ) ^ lamJ j i =
      ∏ i ∈ Finset.univ.erase j, (z i : ℂ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [lamJ_of_ne (Finset.ne_of_mem_erase hi), zpow_one]
  rw [he, lamJ_self, zpow_zero]
  ring

/-- The normalized character at `τ_j`, multiplied by `z j q^j`, does not depend on `j`. -/
theorem normalizedCharacter_lamJ {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (j : Fin (n + 2)) :
    (normalizedCharacter hϖ (n + 1) hq z (torusBorel (n + 1) ϖ (lamJ j)) : ℂ) *
        ((z j : ℂ) * (q : ℂ) ^ (j : ℕ)) =
      ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^ (n + 1) * ∏ i, (z i : ℂ) := by
  rw [normalizedCharacter_torusBorel hϖ hq z (lamJ j), Spherical.halfModulus, weight_lamJ]
  set s : ℂ := ((Real.sqrt (q : ℝ) : ℝ) : ℂ) with hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast residueCardinality_pos hq
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq0).ne'
  have hsq : s ^ 2 = (q : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
    push_cast
    rfl
  have hpow : s ^ ((n : ℤ) + 1 - 2 * ((j : ℕ) : ℤ)) * (q : ℂ) ^ (j : ℕ) = s ^ (n + 1) := by
    rw [← hsq, ← pow_mul, ← zpow_natCast s (n + 1),
      ← zpow_natCast s (2 * (j : ℕ)), ← zpow_add₀ hs0]
    congr 1
    push_cast
    ring
  calc s ^ ((n : ℤ) + 1 - 2 * ((j : ℕ) : ℤ)) * (∏ i, (z i : ℂ) ^ lamJ j i) *
        ((z j : ℂ) * (q : ℂ) ^ (j : ℕ)) =
      (s ^ ((n : ℤ) + 1 - 2 * ((j : ℕ) : ℤ)) * (q : ℂ) ^ (j : ℕ)) *
        ((∏ i, (z i : ℂ) ^ lamJ j i) * (z j : ℂ)) := by ring
    _ = s ^ (n + 1) * ∏ i, (z i : ℂ) := by rw [hpow, prod_lamJ]

/-! ### The cell lemma -/

/-- Right invariance under the parahoric subgroup. -/
def IsParahoricInvariant {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (n + 2) → ℂˣ} (f : PrincipalSeries hϖ (n + 1) hq z) : Prop :=
  ∀ k ∈ parahoric ϖ, ∀ g, value hϖ (n + 1) f (g * k) = value hϖ (n + 1) f g

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem clearMat_mul_self {β : Fin (n + 2) → F} {m : Fin (n + 2)} (hβ : β m = 0) :
    vecMulVec β (Pi.single m (1 : F)) * vecMulVec β (Pi.single m (1 : F)) = 0 := by
  rw [vecMulVec_mul_vecMulVec, single_dotProduct, one_mul, hβ, zero_smul]
  ext a b
  simp [vecMulVec_apply]

/-- The unipotent matrix `1 + β e_mᵀ`, for a vector `β` vanishing from `m` on. -/
def unipGL (β : Fin (n + 2) → F) (m : Fin (n + 2)) (hβ : β m = 0) : GL (Fin (n + 2)) F where
  val := 1 + vecMulVec β (Pi.single m 1)
  inv := 1 - vecMulVec β (Pi.single m 1)
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, clearMat_mul_self hβ]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, clearMat_mul_self hβ]
    abel

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem unipGL_mem_borel {β : Fin (n + 2) → F} {m : Fin (n + 2)}
    (hβ : ∀ i, m ≤ i → β i = 0) :
    unipGL β m (hβ m le_rfl) ∈ Borel (F := F) (n + 1) := by
  refine (mem_upperTriangularSubgroup_iff _).2 fun a b hba => ?_
  change (1 + vecMulVec β (Pi.single m (1 : F))) a b = 0
  rw [Matrix.add_apply, one_apply_ne (ne_of_gt hba), vecMulVec_apply, zero_add, Pi.single_apply]
  split_ifs with hb
  · rw [hβ a (hb ▸ hba.le), zero_mul]
  · rw [mul_zero]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem unipGL_mem_integral {β : Fin (n + 2) → F} {m : Fin (n + 2)} (hβm : β m = 0)
    (hint : ∀ i, β i ∈ 𝒪) : unipGL β m hβm ∈ integralSubgroup 𝒪 (n + 1) := by
  have hN : ∀ a b, vecMulVec β (Pi.single m (1 : F)) a b ∈ 𝒪 := by
    intro a b
    rw [vecMulVec_apply, Pi.single_apply]
    split_ifs
    · rw [mul_one]; exact hint a
    · rw [mul_zero]; exact zero_mem _
  have h1 : ∀ a b, (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) a b ∈ 𝒪 := by
    intro a b
    rw [one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine (mem_integralSubgroup 𝒪 (n + 1) _).2 ⟨fun a b => ?_, fun a b => ?_⟩
  · change (1 + vecMulVec β (Pi.single m (1 : F))) a b ∈ 𝒪
    rw [Matrix.add_apply]
    exact add_mem (h1 a b) (hN a b)
  · change (1 - vecMulVec β (Pi.single m (1 : F))) a b ∈ 𝒪
    rw [Matrix.sub_apply]
    exact sub_mem (h1 a b) (hN a b)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem unipGL_mul_apply_zero {β : Fin (n + 2) → F} {m : Fin (n + 2)} (hβm : β m = 0)
    (κ : GL (Fin (n + 2)) F) (r : Fin (n + 2)) :
    (unipGL β m hβm * κ).val r 0 = κ.val r 0 + β r * κ.val m 0 := by
  change ((1 + vecMulVec β (Pi.single m (1 : F))) * κ.val) r 0 = _
  rw [add_mul, one_mul, Matrix.add_apply, vecMulVec_mul, single_vecMul, one_smul, vecMulVec_apply]
  rfl

/-- The vector clearing the first column of `κ` above row `m`. -/
def clearVec (κ : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (m : Fin (n + 2)) : Fin (n + 2) → F :=
  fun i => if i < m then -(κ i 0 / κ m 0) else 0

/-- **Cell lemma.** A parahoric-invariant function takes at an integral matrix `κ` the
value it takes at `w m`, where `m` is the last row whose first-column entry is a unit. -/
theorem value_eq_weyl {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    {f : PrincipalSeries hϖ (n + 1) hq z} (hf : IsParahoricInvariant hϖ f)
    {κ : GL (Fin (n + 2)) F} (hκ : κ ∈ integralSubgroup 𝒪 (n + 1)) {m : Fin (n + 2)}
    (hm : 𝒱 (κ.val m 0) = 1) (hlow : ∀ i, m < i → 𝒱 (κ.val i 0) < 1) :
    value hϖ (n + 1) f κ = value hϖ (n + 1) f (weyl m) := by
  set β := clearVec κ.val m with hβdef
  have hβ : ∀ i, m ≤ i → β i = 0 := fun i hi => if_neg (not_lt.2 hi)
  have hm0 : κ.val m 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hm
    exact zero_ne_one hm
  have hβint : ∀ i, β i ∈ 𝒪 := by
    intro i
    rw [hβdef, clearVec]
    split_ifs
    · apply mem_of_val_le_one
      rw [Valuation.map_neg, map_div₀, hm, div_one]
      exact val_le_one_of_mem (integral_entry hκ i 0)
    · exact zero_mem _
  set u := unipGL β m (hβ m le_rfl) with hu
  have huB := unipGL_mem_borel hβ
  have huK : u ∈ integralSubgroup 𝒪 (n + 1) := unipGL_mem_integral (hβ m le_rfl) hβint
  have hcol : ∀ r, (u * κ).val r 0 = if r < m then 0 else κ.val r 0 := by
    intro r
    rw [hu, unipGL_mul_apply_zero, hβdef, clearVec]
    split_ifs
    · field_simp
      ring
    · ring
  have hk : weyl m * (u * κ) ∈ parahoric ϖ := by
    rw [mem_parahoric_iff hϖ]
    refine ⟨mul_mem (weyl_mem_integral m) (mul_mem huK hκ), fun i => ?_⟩
    rw [colT_apply, Units.val_mul, weyl_mul_val, submatrix_apply, id, hcol]
    by_cases him : i.succ = m
    · rw [← him, Equiv.swap_apply_right, if_pos (Fin.succ_pos i), map_zero]
      exact zero_lt_one
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) him]
      split_ifs with hlt
      · rw [map_zero]
        exact zero_lt_one
      · exact hlow _ (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm him))
  have hdecomp : u * κ = weyl m * (weyl m * (u * κ)) := by
    rw [← mul_assoc, weyl_mul_self, one_mul]
  calc value hϖ (n + 1) f κ =
      value hϖ (n + 1) f ((⟨u, huB⟩ : Borel (F := F) (n + 1)).val * κ) := by
        rw [value_borel_mul, normalizedCharacter_eq_one_of_integral hϖ (n + 1) hq z ⟨u, huB⟩ huK,
          Units.val_one, one_mul]
    _ = value hϖ (n + 1) f (weyl m * (weyl m * (u * κ))) := by
        change value hϖ (n + 1) f (u * κ) = _
        rw [← hdecomp]
    _ = value hϖ (n + 1) f (weyl m) := hf _ hk (weyl m)

/-- Parahoric-invariant functions agreeing at every `w j` are equal. -/
theorem eq_of_weyl {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 2) → ℂˣ}
    {f g : PrincipalSeries hϖ (n + 1) hq z} (hf : IsParahoricInvariant hϖ f)
    (hg : IsParahoricInvariant hϖ g)
    (h : ∀ j, value hϖ (n + 1) f (weyl j) = value hϖ (n + 1) g (weyl j)) : f = g := by
  apply ext_value hϖ
  intro x
  obtain ⟨b, k, rfl⟩ := exists_borel_integral (F := F) (n + 1) x
  rw [value_borel_mul, value_borel_mul]
  congr 1
  have hK := k.property
  set T := Finset.univ.filter (fun i : Fin (n + 2) => 𝒱 (k.val.val i 0) = 1) with hT
  have hne : T.Nonempty := by
    by_contra hT0
    rw [Finset.not_nonempty_iff_eq_empty] at hT0
    have hsmall : ∀ i, 𝒱 (k.val.val i 0) < 1 := by
      intro i
      refine lt_of_le_of_ne (val_le_one_of_mem (integral_entry hK i 0)) fun hi => ?_
      have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      rw [hT0] at hiT
      simp at hiT
    have hdet := Unramified.MinusculeCosets.valuation_det_eq_one hK
    have h1 := val_det_sub_head_mul_lt k.val.val (integral_entry hK) (fun i => hsmall i.succ)
    have h2 : 𝒱 (k.val.val 0 0 * (low k.val.val).det) < 1 := by
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le (hsmall 0)
        (val_le_one_of_mem (Cartan.det_mem_integer (low k.val.val)
          fun a b => integral_entry hK _ _))
    have h3 := Valuation.map_add_lt 𝒱 h1 h2
    rw [sub_add_cancel] at h3
    have h4 : 𝒱 (k.val.val).det = 1 := hdet
    rw [h4] at h3
    exact lt_irrefl _ h3
  have hm : 𝒱 (k.val.val (T.max' hne) 0) = 1 := (Finset.mem_filter.1 (T.max'_mem hne)).2
  have hlow : ∀ i, T.max' hne < i → 𝒱 (k.val.val i 0) < 1 := by
    intro i hi
    refine lt_of_le_of_ne (val_le_one_of_mem (integral_entry hK i 0)) fun h1 => ?_
    have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    exact absurd (T.le_max' i hiT) (not_le.2 hi)
  rw [value_eq_weyl hϖ hf hK hm hlow, value_eq_weyl hϖ hg hK hm hlow, h]

end Langlands.Conductor.SphericalCyclicity
