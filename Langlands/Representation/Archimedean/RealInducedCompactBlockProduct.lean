import Langlands.Representation.Archimedean.RealInductionStagesInduce
import Langlands.Representation.Archimedean.RealLeviProducts

/-! # Induced operators on pure compact block products -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean
open RealLeviChart RealLeviSlices RealLeviProducts

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ

section Geometry

variable {c : ℕ} (s : Fin c → ℕ) (i : Fin c)
  (h : start s i + s i ≤ ∑ j, s j)

private theorem idx_eq_pos (a : Fin (s i)) : idx h a = pos s i a :=
  Fin.ext (by rw [idx_val, val_pos])

include h in
private theorem not_isMid_pos {j : Fin c} (hj : j ≠ i) (a : Fin (s j)) :
    ¬IsMid (start s i) (s i) (pos s j a) := by
  intro ha
  obtain ⟨a', he⟩ := exists_idx_of_isMid h ha
  rw [idx_eq_pos s i h] at he
  exact hj (by simpa only [cls_pos] using congrArg (cls s) he)

private theorem pos_ne_of_class_ne {j k : Fin c} (hjk : j ≠ k) (a : Fin (s j))
    (b : Fin (s k)) : pos s j a ≠ pos s k b := by
  intro he
  exact hjk (by simpa only [cls_pos] using congrArg (cls s) he)

/-- The block diagonal embedding with one variable block agrees with the
coordinate embedding used for normalized slices. -/
theorem emb_eq_blockEmb (g : G (s i)) : emb s i g = blockEmb h g := by
  apply Units.ext
  rw [emb_val, blockEmb_val, embA]
  ext p q
  obtain ⟨⟨j, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨k, b⟩, rfl⟩ := finSigmaFinEquiv.surjective q
  change blockDiagHom s _ (pos s j a) (pos s k b) = blockMat _ _ _ _ (pos s j a) (pos s k b)
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      rw [blockDiagHom_pos_pos_self, Pi.mulSingle_eq_same, ← idx_eq_pos s i h a,
        ← idx_eq_pos s i h b, blockMat_apply_idx h]
    · rw [blockDiagHom_pos_pos_of_ne s _ (Ne.symm hk),
        blockMat_apply_of_not_isMid_right _ _ (not_isMid_pos s i h hk b),
        Matrix.one_apply_ne (pos_ne_of_class_ne s (Ne.symm hk) a b)]
  · rw [blockMat_apply_of_not_isMid_left _ (not_isMid_pos s i h hj a)]
    by_cases hk : j = k
    · subst k
      have he : pos s j a = pos s j b ↔ a = b := by
        simp only [Fin.ext_iff, val_pos, Nat.add_left_cancel_iff]
      simp only [blockDiagHom_pos_pos_self, Pi.mulSingle_eq_of_ne hj, Matrix.one_apply, he]
    · rw [blockDiagHom_pos_pos_of_ne s _ hk, Matrix.one_apply_ne (pos_ne_of_class_ne s hk a b)]

end Geometry

/-- If a standard vector restricts to a pure block product, applying an induced
middle operator changes just its middle factor on the block-diagonal compact group. -/
def RealInducedCompactBlockProductStatement : Prop :=
  ∀ {c : ℕ} (s : Fin c → ℕ) (i : Fin c) {pre ds es post : List RealBlock}
    (h : start s i + s i ≤ ∑ j, s j)
    (ha : realRank pre = start s i) (hd : realRank ds = s i)
    (he : realRank es = s i) (hn : realRank (pre ++ es ++ post) = ∑ j, s j)
    (T : KFin (s i) ds →ₗ[ℂ] KFin (s i) es)
    (hT : ∀ k f, T (kRep (s i) ds k f) = kRep (s i) es k (T f))
    (F : KFin (∑ j, s j) (pre ++ ds ++ post))
    (f : ∀ j, Langlands.GeneralLinear (s j) ℝ → ℂ) (v : KFin (s i) ds),
    f i = v.val →
    (∀ κ : ∀ j, unitaryCompact ℝ (s j),
      F.val (blockDiagGL s (fun j => (κ j).val)) = ∏ j, f j (κ j).val) →
    ∀ κ : ∀ j, unitaryCompact ℝ (s j),
      (ind h ha he hd hn T hT F).val (blockDiagGL s (fun j => (κ j).val)) =
        (T v).val (κ i).val * ∏ j ∈ Finset.univ \ {i}, f j (κ j).val

theorem realInducedCompactBlockProduct : RealInducedCompactBlockProductStatement := by
  intro c s i pre ds es post h ha hd he hn T hT F f v hv hF κ
  let k : ∀ j, G (s j) := fun j => (κ j).val
  let bd : unitaryCompact ℝ (∑ j, s j) :=
    ⟨blockDiagGL s k, blockDiagGL_mem_unitaryCompact κ⟩
  let C : ℂ := ∏ j ∈ Finset.univ \ {i}, f j (k j)
  have hSlice : sliceK h ha hd bd F = C • kRep (s i) ds (κ i) v := by
    apply Subtype.ext
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
      (sliceK h ha hd bd F).2.1.1 (C • kRep (s i) ds (κ i) v).2.1.1 fun l hl => ?_
    change slice h bd F.val l = C * (kRep (s i) ds (κ i) v).val l
    rw [slice_apply, sliceFactor_of_mem_unitaryCompact hl, one_mul]
    change F.val (blockEmb h l * blockDiagGL s k) = _
    rw [← emb_eq_blockEmb s i h l, emb_mul_blockDiagGL]
    let kl : ∀ j, unitaryCompact ℝ (s j) :=
      Function.update κ i (⟨l, hl⟩ * κ i)
    have hkl : (fun j => (kl j).val) = Function.update k i (l * k i) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [kl, k]
      · simp [kl, Function.update_of_ne hj, k]
    have hprod := congrArg (fun y : ∀ j, G (s j) => ∏ j, f j (y j)) hkl
    rw [← hkl, hF kl, hprod, prod_apply_update, hv, kRep_apply_coe]
    exact mul_comm _ _
  change (ind h ha he hd hn T hT F).val bd = (T v).val (k i) * C
  rw [ind_apply_unitaryCompact, hSlice, map_smul, hT, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, kRep_apply_coe, one_mul]
  exact mul_comm _ _

end Langlands.Archimedean.InductionStages
