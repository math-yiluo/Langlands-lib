import Langlands.BushnellKutzko.LevelZeroSwapMembership
import Mathlib.Data.Matrix.PEquiv

/-! # The block transposition and the lower root block of `U^1(𝔄)` -/

open Matrix ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] {e f : ℕ}

/-- The permutation of indices exchanging two blocks. -/
def blockSwap (i j : Fin e) : Equiv.Perm (Fin f × Fin e) :=
  Equiv.prodCongr (Equiv.refl (Fin f)) (Equiv.swap i j)

@[simp] theorem blockSwap_apply (i j : Fin e) (p : Fin f × Fin e) :
    blockSwap (f := f) i j p = (p.1, Equiv.swap i j p.2) := rfl

theorem blockSwap_symm (i j : Fin e) : (blockSwap (f := f) i j).symm = blockSwap i j := by
  ext p <;> simp [blockSwap]

theorem pairEmb_swap_eq {i j : Fin e} (hij : i ≠ j) :
    pairEmb F (f := f) hij (fromBlocks 0 1 1 0) = (blockSwap (f := f) i j).toPEquiv.toMatrix := by
  ext p q
  refine pairEmb_forall hij (fromBlocks 0 1 1 0)
    (fun p q x => x = (blockSwap (f := f) i j).toPEquiv.toMatrix p q) ?_ ?_ ?_ ?_ ?_ p q
  · intro a b
    simp [PEquiv.toMatrix_apply, Ne.symm hij]
  · intro a b
    simp [PEquiv.toMatrix_apply, Matrix.one_apply, Prod.ext_iff]
  · intro a b
    simp [PEquiv.toMatrix_apply, Matrix.one_apply, Prod.ext_iff]
  · intro a b
    simp [PEquiv.toMatrix_apply, hij]
  · rintro ⟨a, k⟩ ⟨b, l⟩ h
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      blockSwap_apply]
    rcases h with ⟨hki, hkj⟩ | ⟨hli, hlj⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      by_cases hpq : (a, k) = (b, l)
      · rw [hpq]; simp
      · rw [Matrix.one_apply_ne hpq, ite_eq_right hpq]
    · by_cases hki : k = i
      · subst hki
        rw [Equiv.swap_apply_left, Matrix.one_apply_ne (fun h => hli (congrArg Prod.snd h).symm),
          ite_eq_right (fun h => hlj (congrArg Prod.snd h).symm)]
      · by_cases hkj : k = j
        · subst hkj
          rw [Equiv.swap_apply_right,
            Matrix.one_apply_ne (fun h => hlj (congrArg Prod.snd h).symm),
            ite_eq_right (fun h => hli (congrArg Prod.snd h).symm)]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
          by_cases hpq : (a, k) = (b, l)
          · rw [hpq]; simp
          · rw [Matrix.one_apply_ne hpq, ite_eq_right hpq]

/-- Conjugation by the block transposition permutes the entries. -/
theorem pairEmb_swap_conj {i j : Fin e} (hij : i ≠ j) (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    pairEmb F hij (fromBlocks 0 1 1 0) * x * pairEmb F hij (fromBlocks 0 1 1 0) =
      x.submatrix (blockSwap i j) (blockSwap i j) := by
  rw [pairEmb_swap_eq, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    blockSwap_symm]
  rfl

section Theta

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem val_le_one_of_mem_J0 {g : GL (Fin f × Fin e) F} (hg : g ∈ J0 F e f) (p q : Fin f × Fin e) :
    valuation F ((g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q) ≤ 1 :=
  (hg.1 p q).1

theorem res_one_apply (p q : Fin f × Fin e) :
    res ((1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q) = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h; simp
  · rw [Matrix.one_apply_ne h, ite_eq_right h, res_zero]

theorem res_of_mem_J1_diag {g : GL (Fin f × Fin e) F} (hg : g ∈ J1 F e f) (a b : Fin f)
    (k : Fin e) :
    res ((g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, k) (b, k)) =
      (1 : Matrix (Fin f) (Fin f) 𝓀[F]) a b := by
  have h := (hg.2 (a, k) (b, k)).2 le_rfl
  rw [Matrix.sub_apply] at h
  have h1 : valuation F ((1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, k) (b, k)) ≤ 1 := by
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne (fun h => hab (congrArg Prod.fst h)), map_zero]; exact zero_le
  rw [(res_eq_res_iff (val_le_one_of_mem_J0 hg.1 _ _) h1).mpr h, res_one_apply,
    Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [ite_eq_right (fun h => hab (congrArg Prod.fst h)), ite_eq_right hab]

theorem res_of_mem_J0_upper {g : GL (Fin f × Fin e) F} (hg : g ∈ J0 F e f) {k l : Fin e}
    (hkl : k < l) (a b : Fin f) :
    res ((g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, k) (b, l)) = 0 :=
  (res_eq_zero_iff (val_le_one_of_mem_J0 hg _ _)).mpr ((hg.1 (a, k) (b, l)).2 hkl)

/-- The residue of the lower block in position `(j, i)`. -/
def thetaFun (i j : Fin e) (g : GL (Fin f × Fin e) F) : Matrix (Fin f) (Fin f) 𝓀[F] :=
  fun a b => res ((g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, j) (b, i))

theorem thetaFun_mul {i j : Fin e} (hij : i.val + 1 = j.val) {g h : GL (Fin f × Fin e) F}
    (hg : g ∈ J1 F e f) (hh : h ∈ J1 F e f) :
    thetaFun i j (g * h) = thetaFun i j g + thetaFun i j h := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  ext a b
  simp only [thetaFun, Units.val_mul, Matrix.mul_apply, Matrix.add_apply]
  rw [res_sum _ _ fun r _ => by
    rw [map_mul]; exact mul_le_one' (val_le_one_of_mem_J0 hg.1 _ _) (val_le_one_of_mem_J0 hh.1 _ _)]
  rw [Finset.sum_congr rfl fun r _ =>
    res_mul (val_le_one_of_mem_J0 hg.1 (a, j) r) (val_le_one_of_mem_J0 hh.1 r (b, i))]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun c _ => Fintype.sum_eq_add i j hne fun k hk => by
    rcases lt_or_gt_of_ne hk.1 with hki | hki
    · rw [res_of_mem_J0_upper hh.1 hki, mul_zero]
    · have hjk : j < k := by
        rw [Fin.lt_def] at hki ⊢
        have := hk.2
        rw [Ne, Fin.ext_iff] at this
        omega
      rw [res_of_mem_J0_upper hg.1 hjk, zero_mul]]
  simp only [res_of_mem_J1_diag hg, res_of_mem_J1_diag hh, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The lower block in position `(j, i)` modulo the maximal ideal, as an additive
character of `U^1(𝔄)` with values in matrices over the residue field. -/
def thetaHom {i j : Fin e} (hij : i.val + 1 = j.val) :
    J1 F e f →* Multiplicative (Matrix (Fin f) (Fin f) 𝓀[F]) where
  toFun g := Multiplicative.ofAdd (thetaFun i j (g : GL (Fin f × Fin e) F))
  map_one' := by
    have hne : j ≠ i := fun h => by rw [h] at hij; omega
    apply congrArg Multiplicative.ofAdd
    ext a b
    simp only [thetaFun, OneMemClass.coe_one, Units.val_one]
    rw [Matrix.one_apply_ne (fun h => hne (congrArg Prod.snd h)), res_zero]
    rfl
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [thetaFun_mul hij g.2 h.2]
    rfl

theorem thetaHom_apply {i j : Fin e} (hij : i.val + 1 = j.val) (g : J1 F e f) (a b : Fin f) :
    Multiplicative.toAdd (thetaHom hij g) a b =
      res (((g : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, j) (b, i)) :=
  rfl

theorem mem_ker_thetaHom {i j : Fin e} (hij : i.val + 1 = j.val) (g : J1 F e f) :
    g ∈ (thetaHom hij).ker ↔
      ∀ a b, valuation F (((g : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F)
        (a, j) (b, i)) < 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a b
    have h' : res (((g : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F)
        (a, j) (b, i)) = 0 := congrFun (congrFun (congrArg Multiplicative.toAdd h) a) b
    exact (res_eq_zero_iff (val_le_one_of_mem_J0 g.2.1 _ _)).mp h'
  · intro h
    apply congrArg Multiplicative.ofAdd
    ext a b
    exact (res_eq_zero_iff (val_le_one_of_mem_J0 g.2.1 _ _)).mpr (h a b)

private theorem swap_order {i j k l : Fin e} (hij : i.val + 1 = j.val) (hkl : k ≤ l)
    (h : ¬ Equiv.swap i j k ≤ Equiv.swap i j l) : k = i ∧ l = j := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at h
  rw [Fin.le_def] at hkl
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    simp only [Fin.le_def, not_le] at h <;>
    simp only [Fin.ext_iff] at * <;> omega

/-- Conjugation by the block transposition keeps the kernel of `thetaHom` in `U^1(𝔄)`. -/
theorem swap_conj_mem_J1 {i j : Fin e} (hij : i.val + 1 = j.val)
    {l : J1 F e f} (hl : l ∈ (thetaHom hij).ker) :
    have hlt : i < j := by rw [Fin.lt_def]; omega
    pairGL hlt.ne swapU * (l : GL (Fin f × Fin e) F) * pairGL hlt.ne swapU ∈ J1 F e f := by
  intro hlt
  have key : ∀ m : J1 F e f, m ∈ (thetaHom hij).ker →
      InRad (((pairGL hlt.ne swapU * (m : GL (Fin f × Fin e) F) * pairGL hlt.ne swapU :
        GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) - 1) := by
    intro m hm
    have hm' := (mem_ker_thetaHom hij m).mp hm
    simp only [Units.val_mul, coe_pairGL, coe_swapU]
    rw [pairEmb_swap_conj, ← Matrix.submatrix_one_equiv (blockSwap (f := f) i j)]
    intro p q
    have hrad := m.2.2 (blockSwap (f := f) i j p) (blockSwap (f := f) i j q)
    simp only [Matrix.sub_apply, Matrix.submatrix_apply] at hrad ⊢
    refine ⟨hrad.1, fun hpq => ?_⟩
    by_cases hord : (blockSwap (f := f) i j p).2 ≤ (blockSwap (f := f) i j q).2
    · exact hrad.2 hord
    · obtain ⟨hpi, hqj⟩ := swap_order hij hpq hord
      obtain ⟨a, k⟩ := p
      obtain ⟨b, l⟩ := q
      simp only at hpi hqj
      rw [hpi, hqj]
      have e1 : blockSwap (f := f) i j (a, i) = (a, j) := by simp
      have e2 : blockSwap (f := f) i j (b, j) = (b, i) := by simp
      rw [e1, e2, Matrix.one_apply_ne (fun h => hlt.ne (congrArg Prod.snd h).symm), sub_zero]
      exact hm' a b
  refine mem_J1_of_inRad (key l hl) ?_
  have hinv : (pairGL hlt.ne swapU * (l : GL (Fin f × Fin e) F) * pairGL hlt.ne swapU)⁻¹ =
      pairGL hlt.ne swapU * ((l⁻¹ : J1 F e f) : GL (Fin f × Fin e) F) * pairGL hlt.ne swapU := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, swapU_inv, mul_assoc, InvMemClass.coe_inv]
  rw [hinv]
  exact key l⁻¹ ((thetaHom hij).ker.inv_mem hl)

end Theta

end Langlands.BushnellKutzko.LevelZero
