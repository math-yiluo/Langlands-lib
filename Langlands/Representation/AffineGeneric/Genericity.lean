import Langlands.Representation.AffineGeneric.Decomposition
import Langlands.Representation.LevelZero.JacquetVanishing
import Langlands.Representation.Aubert.CutTransitionMaps

/-!
# Cyclic linear forms on `I⁺` and proper unipotent radicals

For `ϖ : Fˣ` and `r : Fin (m + 1) → k`, the cyclic linear form
`λ_r(g) = Σ_i r_i a_i(g - 1)` is defined using the coordinates `groupCoord ϖ g i`.
For a uniformizer `ϖ`, it is additive on `I⁺`, so `ψ ∘ λ_r` is a character for an additive
character `ψ` of `k`. If also `m ≥ 1`, `ψ` is nontrivial and every `r_i` is nonzero, the
character is affine generic. Knightly–Li (Section 2) give this explicit form for `GL_n`, and
Gross–Reeder (Section 9.2) give the root-theoretic definition for split simply connected
almost simple groups.

For a uniformizer `ϖ` and all `r_i` nonzero, the form takes every value of `k` on
`x U x⁻¹ ∩ I⁺` for any `x ∈ GL_{m+1}(F)` and any proper standard block parabolic with
unipotent radical `U`. This intersection lemma gives vanishing constant terms in
`TestFunction` and vanishing Jacquet coinvariants in `Supercuspidality`. For `m = 0` the
assertion about proper block parabolics is vacuous.

The proof writes `x = ι w β b⁻¹` (`exists_iwahori_decomposition`), finds an index `s` with
`w⁻¹ s` in a strictly earlier block than `w⁻¹ (ρ s)`, where `ρ = finRotate (m + 1)`
(`exists_blockIndex_lt_finRotate`), and conjugates an element of `I⁺` of the form
`1 + Y`, with `Y` supported at `(s, ρ s)`, into `U`.
-/

noncomputable section

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear

universe u

variable {F : Type u} [Field F] [ValuativeRel F] {m : ℕ}

/-! ### A cyclic separation lemma for block shapes -/

/-- For a block shape with at least two blocks and a permutation `v`, some cyclically
consecutive pair `s, s + 1` is sent by `v` to strictly increasing blocks. -/
theorem exists_blockIndex_lt_finRotate (B : BlockShape (m + 1)) (hB : 2 ≤ B.length)
    (v : Equiv.Perm (Fin (m + 1))) :
    ∃ s, Geometric.blockIndex B (v s) < Geometric.blockIndex B (v (finRotate (m + 1) s)) := by
  by_contra h
  push Not at h
  let f : Fin (m + 1) → Fin B.length := fun s => Geometric.blockIndex B (v s)
  have hstep : ∀ s, f (finRotate (m + 1) s) ≤ f s := h
  have hanti : Antitone f := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have hr : finRotate (m + 1) (Fin.castSucc i) = i.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
      simp
    have := hstep (Fin.castSucc i)
    rwa [hr] at this
  have hconst : ∀ s, f s = f 0 := by
    intro s
    apply le_antisymm (hanti (Fin.zero_le s))
    calc f 0 = f (finRotate (m + 1) (Fin.last m)) := by rw [finRotate_last]
      _ ≤ f (Fin.last m) := hstep _
      _ ≤ f s := hanti (Fin.le_last s)
  have hsurj : ∀ i : Fin B.length, ∃ s, f s = i := by
    intro i
    refine ⟨v⁻¹ (B.index i ⟨0, B.positive i⟩), ?_⟩
    simp only [f, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply,
      Geometric.blockIndex_index]
  obtain ⟨s0, hs0⟩ := hsurj ⟨0, by omega⟩
  obtain ⟨s1, hs1⟩ := hsurj ⟨1, by omega⟩
  have h01 := (hconst s0).trans (hconst s1).symm
  rw [hs0, hs1] at h01
  exact absurd (congrArg Fin.val h01) (by simp)

/-! ### Upper triangular matrices lie in every standard parabolic -/

theorem upperTriangular_mem_parabolic {R : Type*} [CommRing R] {n : ℕ} (B : BlockShape n)
    {g : GeneralLinear n R} (hg : ∀ i j : Fin n, j < i → g i j = 0) : g ∈ B.parabolic R := by
  rw [Geometric.mem_parabolic_iff_blockIndex R B g]
  intro a b hab
  exact hg a b (lt_of_not_ge fun h => (not_le.mpr hab) (Geometric.blockIndex_monotone B h))

/-! ### Elements of `I⁺` with a prescribed radical part -/

/-- Every element `Y` of the radical `𝔓` gives an element `1 + Y` of `I⁺`. -/
theorem exists_mem_iwahoriRadical_coe_eq {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) :
    ∃ g : GeneralLinear (m + 1) F, g ∈ iwahoriRadical m ∧
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + Y := by
  have hint : ∀ i j, (1 + Y) i j ∈ integers F := fun i j =>
    (Valuation.mem_integer_iff _ _).mpr
      ((valuation F).map_add_le (isIwahoriOrder_one i j).1 (hY i j).1)
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) (integers F) := fun i j => ⟨(1 + Y) i j, hint i j⟩
  have hlower : ∀ i j, j < i → resOf ((1 + Y) i j) = 0 := by
    intro i j hji
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), zero_add]
    exact resOf_of_lt_one ((hY i j).2 hji.le)
  have hdiag : ∀ i, resOf ((1 + Y) i i) = 1 := by
    intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq,
      resOf_add_of_lt_one (by simp) ((hY i i).2 le_rfl), resOf_one]
  have hres : ∀ i j, IsLocalRing.residue (integers F) (A i j) = resOf ((1 + Y) i j) :=
    fun i j => (resOf_coe (A i j)).symm
  have hdet : IsUnit A.det := by
    apply isUnit_of_map_unit (IsLocalRing.residue (integers F))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_isUpperTriangular]
    · simp only [Matrix.map_apply, hres, hdiag, Finset.prod_const_one, isUnit_one]
    · intro i j hij
      simp only [Matrix.map_apply, hres]
      exact hlower i j hij
  let h : GeneralLinearGroup (Fin (m + 1)) (integers F) := Matrix.nonsingInvUnit A hdet
  let g : Conductor.integralSubgroup (integers F) m :=
    IntegralReduction.integralEquiv (integers F) m h
  have hentry : ∀ i j, (g : GeneralLinear (m + 1) F) i j = (1 + Y) i j := fun _ _ => rfl
  have hg : ((g : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + Y := by
    ext i j
    exact hentry i j
  have hredg : ∀ i j : Fin (m + 1), j < i →
      IntegralReduction.reduction (integers F) m g i j = 0 := by
    intro i j hji
    rw [← resOf_entry, hentry]
    exact hlower i j hji
  have hgi : IsIwahoriOrder
      (((g⁻¹ : Conductor.integralSubgroup (integers F) m) : GeneralLinear (m + 1) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    isIwahoriOrder_of_reduction g⁻¹ (fun i j hji => by
      rw [map_inv]
      exact inv_upperTriangular _ hredg i j hji)
  refine ⟨(g : GeneralLinear (m + 1) F), ⟨?_, ?_⟩, hg⟩
  · rw [hg, add_sub_cancel_left]
    exact hY
  · have h1 : (((g : GeneralLinear (m + 1) F)⁻¹ : GeneralLinear (m + 1) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 + Y) = 1 := by
      rw [← hg]
      exact coe_inv_mul_coe
    have h2 : (((g : GeneralLinear (m + 1) F)⁻¹ : GeneralLinear (m + 1) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 =
        -((((g : GeneralLinear (m + 1) F)⁻¹ : GeneralLinear (m + 1) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Y) := by
      rw [Matrix.mul_add, Matrix.mul_one] at h1
      rw [← h1]
      abel
    rw [h2]
    exact (hgi.mul_radical hY).neg

/-! ### Elementary elements of the radical -/

omit [ValuativeRel F] in
theorem weight_ne_zero (ϖ : Fˣ) (i : Fin (m + 1)) : weight ϖ i ≠ 0 := by
  unfold weight
  split_ifs
  · exact inv_ne_zero ϖ.ne_zero
  · exact one_ne_zero

/-- The coordinates of the elementary matrix supported at `(s, ρ s)` with weighted entry `c`,
where `ρ = finRotate (m + 1)`. -/
theorem coord_single (ϖ : Fˣ) (s : Fin (m + 1)) (c : F) (i : Fin (m + 1)) :
    coord ϖ (Matrix.single s (finRotate (m + 1) s) ((weight ϖ s)⁻¹ * c)) i =
      if i = s then resOf c else 0 := by
  unfold coord
  split_ifs with h
  · subst h
    rw [Matrix.single_apply_same, ← mul_assoc, mul_inv_cancel₀ (weight_ne_zero ϖ i), one_mul]
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h h'.1.symm), mul_zero, resOf_zero]

variable {ϖ : Fˣ} (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
include hϖ

theorem isIwahoriRadical_single (s : Fin (m + 1)) {c : F} (hc : valuation F c ≤ 1) :
    IsIwahoriRadical (Matrix.single s (finRotate (m + 1) s) ((weight ϖ s)⁻¹ * c)) := by
  intro i j
  by_cases h : s = i ∧ finRotate (m + 1) s = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same]
    unfold weight
    split_ifs with hs
    · rw [inv_inv]
      have hlt : valuation F ((ϖ : F) * c) < 1 := val_mul_lt_one_left hϖ.1 hc
      exact ⟨hlt.le, fun _ => hlt⟩
    · rw [inv_one, one_mul]
      exact ⟨hc, fun hle => absurd hle (not_le.mpr (lt_finRotate_of_ne_last hs))⟩
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h]
    exact ⟨by simp, fun _ => by simp⟩

omit hϖ

/-! ### Cyclic linear forms -/

variable (ϖ)

/-- The cyclic linear form `λ_r(g) = Σ_i r_i a_i(g - 1)` for `ϖ : Fˣ` and
`r : Fin (m + 1) → k`. For a uniformizer `ϖ`, it is additive on `I⁺`. Then `ψ ∘ λ_r` is a
character of `I⁺` for each additive character `ψ` of `k`. It is affine generic when `m ≥ 1`,
`ψ` is nontrivial and every `r_i ≠ 0`. -/
def affineForm (r : Fin (m + 1) → Residue F) (g : GeneralLinear (m + 1) F) : Residue F :=
  ∑ i, r i * groupCoord ϖ g i

variable {ϖ}

include hϖ

theorem affineForm_mul (r : Fin (m + 1) → Residue F) {g h : GeneralLinear (m + 1) F}
    (hg : g ∈ iwahoriRadical m) (hh : h ∈ iwahoriRadical m) :
    affineForm ϖ r (g * h) = affineForm ϖ r g + affineForm ϖ r h := by
  unfold affineForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupCoord_mul hϖ hg hh, mul_add]

/-- **Genericity.** For a uniformizer `ϖ` and all `r_i` nonzero, the form `λ_r` takes every
value on `x U x⁻¹ ∩ I⁺` for any `x` and any proper standard block unipotent radical `U`. -/
theorem exists_unipotent_affineForm_eq (r : Fin (m + 1) → Residue F) (hr : ∀ i, r i ≠ 0)
    (t : Residue F) (x : GeneralLinear (m + 1) F) (B : BlockShape (m + 1))
    (hB : 2 ≤ B.length) :
    ∃ u ∈ B.unipotentSubgroup F, x * u * x⁻¹ ∈ iwahoriRadical m ∧
      affineForm ϖ r (x * u * x⁻¹) = t := by
  obtain ⟨ι, w, β, b, hι, hι', hβ, hb, hx⟩ := exists_iwahori_decomposition x
  obtain ⟨s, hs⟩ := exists_blockIndex_lt_finRotate B hB w⁻¹
  have hdiag : ∀ i, resOf ((ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) *
      resOf (((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) =
        1 := by
    intro i
    rw [← hι.resOf_mul_diag hι' i, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq, resOf_one]
  obtain ⟨e, he_def⟩ : ∃ e : Residue F, e = r s *
      resOf ((ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) s s) *
      resOf (((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        (finRotate (m + 1) s) (finRotate (m + 1) s)) := ⟨_, rfl⟩
  have he : e ≠ 0 := by
    rw [he_def]
    exact mul_ne_zero (mul_ne_zero (hr s) (left_ne_zero_of_mul_eq_one (hdiag s)))
      (right_ne_zero_of_mul_eq_one (hdiag (finRotate (m + 1) s)))
  obtain ⟨c0, hc0, hres⟩ := exists_resOf_eq (t / e)
  have hY := isIwahoriRadical_single hϖ s hc0
  obtain ⟨E, hE, hEY⟩ := exists_mem_iwahoriRadical_coe_eq hY
  have hEentry : ∀ i j, E i j = (1 + Matrix.single s (finRotate (m + 1) s)
      ((weight ϖ s)⁻¹ * c0)) i j := fun i j => by
    rw [← hEY]
  have hconj : x * ((β * b⁻¹)⁻¹ * ((permutation (m + 1) F w)⁻¹ * E *
      permutation (m + 1) F w) * (β * b⁻¹)) * x⁻¹ = ι * E * ι⁻¹ := by
    rw [hx]
    group
  refine ⟨(β * b⁻¹)⁻¹ * ((permutation (m + 1) F w)⁻¹ * E * permutation (m + 1) F w) *
    (β * b⁻¹), ?_, ?_, ?_⟩
  · have hq : β * b⁻¹ ∈ B.parabolic F :=
      mul_mem (upperTriangular_mem_parabolic B hβ)
        (inv_mem (upperTriangular_mem_parabolic B hb))
    have hPE : (permutation (m + 1) F w)⁻¹ * E * permutation (m + 1) F w ∈
        B.unipotentSubgroup F := by
      rw [Aubert.mem_unipotentSubgroup_iff_blockIndex]
      intro a c hle
      have he' : (permutation (m + 1) F w)⁻¹ * E * permutation (m + 1) F w =
          permutation (m + 1) F w⁻¹ * E * (permutation (m + 1) F w⁻¹)⁻¹ := by
        rw [permutation_inv, permutation_inv, inv_inv]
      rw [he', permutation_conjugate_entry, inv_inv, hEentry, Matrix.add_apply,
        Matrix.single_apply_of_ne, add_zero, Matrix.one_apply]
      · simp only [w.injective.eq_iff]
      · rintro ⟨h1, h2⟩
        have ha : a = w⁻¹ s := (Equiv.Perm.inv_eq_iff_eq.mpr h1).symm
        have hc : c = w⁻¹ (finRotate (m + 1) s) := (Equiv.Perm.inv_eq_iff_eq.mpr h2).symm
        rw [ha, hc] at hle
        exact absurd hle (not_le.mpr hs)
    have := B.conj_mem_unipotentSubgroup (inv_mem hq) hPE
    rwa [inv_inv] at this
  · rw [hconj]
    exact conj_mem_iwahoriRadical hι hι' hE
  · rw [hconj]
    unfold affineForm
    have hcoordE : ∀ i, groupCoord ϖ E i = if i = s then t / e else 0 := by
      intro i
      unfold groupCoord
      rw [hEY, add_sub_cancel_left, coord_single, hres]
    rw [Finset.sum_eq_single s]
    · rw [groupCoord_conj hϖ hι hι' hE, hcoordE]
      simp only [↓reduceIte]
      have key : r s * (resOf ((ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) s s) * (t / e) *
          resOf (((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
            (finRotate (m + 1) s) (finRotate (m + 1) s))) = e * (t / e) := by
        rw [he_def]
        ring
      rw [key, mul_div_cancel₀ t he]
    · intro i _ hi
      rw [groupCoord_conj hϖ hι hι' hE, hcoordE]
      simp only [hi, ↓reduceIte, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ s) h

end Langlands.AffineGeneric
