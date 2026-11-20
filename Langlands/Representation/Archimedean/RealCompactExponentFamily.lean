import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.ComplexBlockRestriction

/-!
# Real standard modules with one varying exponent

Restriction to `O(n)` identifies the compact pictures for exponent shifts.
In this identification the compact operators are constant and the real
Lie operators are affine. A shift of one list block has the exponent
increment supported on the positions of that block.
-/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealExponentDeformation

open Langlands.LocalFactor.Archimedean GramFormula

variable {n : ℕ} {ds es : List RealBlock}

private def compactTransfer (hr : realRank es = n) (h : IsShapeCompatible ds es) :
    KF n ds →ₗ[ℂ] KF n es where
  toFun f := (exists_eqOn hr h f).choose
  map_add' f g := by
    apply ext_of_eqOn
    intro k hk
    change ((exists_eqOn hr h (f + g)).choose : Langlands.GeneralLinear n ℝ → ℂ) k =
      ((exists_eqOn hr h f).choose : Langlands.GeneralLinear n ℝ → ℂ) k +
      ((exists_eqOn hr h g).choose : Langlands.GeneralLinear n ℝ → ℂ) k
    rw [(exists_eqOn hr h (f + g)).choose_spec hk, (exists_eqOn hr h f).choose_spec hk,
      (exists_eqOn hr h g).choose_spec hk]
    rfl
  map_smul' c f := by
    apply ext_of_eqOn
    intro k hk
    change ((exists_eqOn hr h (c • f)).choose : Langlands.GeneralLinear n ℝ → ℂ) k =
      c * ((exists_eqOn hr h f).choose : Langlands.GeneralLinear n ℝ → ℂ) k
    rw [(exists_eqOn hr h (c • f)).choose_spec hk, (exists_eqOn hr h f).choose_spec hk]
    rfl

private theorem compactTransfer_eqOn (hr : realRank es = n) (h : IsShapeCompatible ds es)
    (f : KF n ds) : Set.EqOn (compactTransfer hr h f : Langlands.GeneralLinear n ℝ → ℂ) f
      (unitaryCompact ℝ n) :=
  (exists_eqOn hr h f).choose_spec

/-- The unique linear equivalence between shape-compatible realizations
that preserves the values of every vector on the compact subgroup. -/
def compactEquiv (hd : realRank ds = n) (he : realRank es = n)
    (h : IsShapeCompatible ds es) (h' : IsShapeCompatible es ds) : KF n ds ≃ₗ[ℂ] KF n es where
  toLinearMap := compactTransfer he h
  invFun := compactTransfer hd h'
  left_inv f := ext_of_eqOn ((compactTransfer_eqOn hd h' _).trans (compactTransfer_eqOn he h f))
  right_inv f := ext_of_eqOn ((compactTransfer_eqOn he h _).trans (compactTransfer_eqOn hd h' f))

theorem compactEquiv_eqOn (hd : realRank ds = n) (he : realRank es = n)
    (h : IsShapeCompatible ds es) (h' : IsShapeCompatible es ds) (f : KF n ds) :
    Set.EqOn (compactEquiv hd he h h' f : Langlands.GeneralLinear n ℝ → ℂ) f (unitaryCompact ℝ n) :=
  compactTransfer_eqOn he h f

theorem compactEquiv_symm_eqOn (hd : realRank ds = n) (he : realRank es = n)
    (h : IsShapeCompatible ds es) (h' : IsShapeCompatible es ds) (f : KF n es) :
    Set.EqOn ((compactEquiv hd he h h').symm f : Langlands.GeneralLinear n ℝ → ℂ) f
      (unitaryCompact ℝ n) :=
  compactTransfer_eqOn hd h' f

theorem compactEquiv_map_rep (hd : realRank ds = n) (he : realRank es = n)
    (h : IsShapeCompatible ds es) (h' : IsShapeCompatible es ds)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds) :
    compactEquiv hd he h h' (realStandardRep n ds k f) =
      realStandardRep n es k (compactEquiv hd he h h' f) := by
  apply ext_of_eqOn
  intro g hg
  rw [compactEquiv_eqOn hd he h h' (realStandardRep n ds k f) hg,
    realStandardRep_apply_coe, realStandardRep_apply_coe]
  exact (compactEquiv_eqOn hd he h h' f ((unitaryCompact ℝ n).mul_mem hg k.2)).symm

/-- The comparison of the base model with each model of the exponent shift. -/
def IsExponentShift.compactEquiv {a : Fin n → ℂ} {z : ℂ} (h : IsExponentShift n ds es a z) :
    KF n ds ≃ₗ[ℂ] KF n es :=
  RealExponentDeformation.compactEquiv h.rank h.rank' h.forward h.backward

theorem IsExponentShift.compactEquiv_map_rep {a : Fin n → ℂ} {z : ℂ}
    (h : IsExponentShift n ds es a z) (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds) :
    h.compactEquiv (realStandardRep n ds k f) = realStandardRep n es k (h.compactEquiv f) :=
  RealExponentDeformation.compactEquiv_map_rep h.rank h.rank' h.forward h.backward k f

/-- The shifted right derivative, transported to the base compact realization. -/
def IsExponentShift.transportedLie {a : Fin n → ℂ} {z : ℂ} (h : IsExponentShift n ds es a z)
    (X : Matrix (Fin n) (Fin n) ℝ) : Module.End ℂ (KF n ds) :=
  h.compactEquiv.symm.toLinearMap ∘ₗ realStandardLie n es (1 ⊗ₜ X) ∘ₗ h.compactEquiv.toLinearMap

private theorem IsExponentShift.transportedLie_apply {a : Fin n → ℂ} {z : ℂ}
    (h : IsExponentShift n ds es a z) (X : Matrix (Fin n) (Fin n) ℝ) (f : KF n ds)
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    (h.transportedLie X f : Langlands.GeneralLinear n ℝ → ℂ) g =
      ((realStandardLie n ds (1 ⊗ₜ X) f : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) g +
        z * diagWeight a X g * (f : Langlands.GeneralLinear n ℝ → ℂ) g := by
  change (h.compactEquiv.symm (realStandardLie n es (1 ⊗ₜ X) (h.compactEquiv f)) :
    Langlands.GeneralLinear n ℝ → ℂ) g = _
  have hback : (h.compactEquiv.symm (realStandardLie n es (1 ⊗ₜ X) (h.compactEquiv f)) :
      Langlands.GeneralLinear n ℝ → ℂ) g =
      (realStandardLie n es (1 ⊗ₜ X) (h.compactEquiv f) : Langlands.GeneralLinear n ℝ → ℂ) g :=
    compactEquiv_symm_eqOn h.rank h.rank' h.forward h.backward _ hg
  rw [hback, realStandardLie_one_tmul_apply_coe, realStandardLie_one_tmul_apply_coe]
  exact rightDerivative_eq_of_exponent_shift h.exponent f.2.1.1 (h.compactEquiv f).2.1.1
    (compactEquiv_eqOn h.rank h.rank' h.forward h.backward f) X hg

/-- The coefficient of a shift in the transported real Lie operator. -/
def lieIncrement {a : Fin n → ℂ} (h₁ : IsExponentShift n ds es a 1)
    (X : Matrix (Fin n) (Fin n) ℝ) : Module.End ℂ (KF n ds) :=
  h₁.transportedLie X - realStandardLie n ds (1 ⊗ₜ X)

theorem transportedLie_eq_affine {a : Fin n → ℂ} {z : ℂ} {et : List RealBlock}
    (h : IsExponentShift n ds es a z) (h₁ : IsExponentShift n ds et a 1)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    h.transportedLie X = realStandardLie n ds (1 ⊗ₜ X) + z • lieIncrement h₁ X := by
  apply LinearMap.ext
  intro f
  apply ext_of_eqOn
  intro g hg
  let eval (w : KF n ds) := (w : Langlands.GeneralLinear n ℝ → ℂ) g
  change eval (h.transportedLie X f) = eval (realStandardLie n ds (1 ⊗ₜ X) f) +
    z * (eval (h₁.transportedLie X f) - eval (realStandardLie n ds (1 ⊗ₜ X) f))
  dsimp only [eval]
  rw [IsExponentShift.transportedLie_apply h X f hg, IsExponentShift.transportedLie_apply h₁ X f hg]
  ring

/-- Shift the complex exponent of a real block, retaining its parity or weight. -/
def shiftBlock (z : ℂ) : RealBlock → RealBlock
  | .character d => .character (RealJacquetFrobenius.charData d.parity (d.exponent + z))
  | .induced d => .induced (ComplexBlock.twist z d)

@[simp]
theorem shiftBlock_rank (z : ℂ) (b : RealBlock) : (shiftBlock z b).rank = b.rank := by
  cases b <;> rfl

private theorem sameShape_refl (b : RealBlock) : SameShape b b := by cases b <;> rfl

private theorem sameShape_shift (z : ℂ) (b : RealBlock) : SameShape b (shiftBlock z b) := by
  cases b <;> rfl

private theorem forall₂_sameShape (l : List RealBlock) : List.Forall₂ SameShape l l := by
  induction l with
  | nil => exact .nil
  | cons b l ih => exact .cons (sameShape_refl b) ih

private theorem singleton_shift_exponent (z : ℂ) (b : RealBlock) (j : ℕ)
    (hj : j < b.rank) :
    realPositionExponent [shiftBlock z b] j = realPositionExponent [b] j + z := by
  cases b with
  | character d =>
    have he : j = 0 := by change j < 1 at hj; omega
    subst j
    rfl
  | induced d =>
    change j < 2 at hj
    rcases j with _ | _ | j
    · change d.exponent + z + (d.weight.natAbs : ℂ) / 2 = _
      change _ = d.exponent + (d.weight.natAbs : ℂ) / 2 + z
      ring
    · change d.exponent + z - (d.weight.natAbs : ℂ) / 2 = _
      change _ = d.exponent - (d.weight.natAbs : ℂ) / 2 + z
      ring
    · omega

private theorem realRank_singleton (b : RealBlock) : realRank [b] = b.rank := by simp

/-- The exponent shift from moving one block acts on exactly its diagonal positions. -/
theorem isExponentShift_shiftBlock (pre post : List RealBlock) (b : RealBlock)
    (hr : realRank (pre ++ b :: post) = n) (z : ℂ) :
    IsExponentShift n (pre ++ b :: post) (pre ++ shiftBlock z b :: post)
      (fun i => if realRank pre ≤ (i : ℕ) ∧ (i : ℕ) < realRank pre + b.rank then 1 else 0) z := by
  refine IsExponentShift.of_forall₂ hr
    (List.rel_append (forall₂_sameShape pre) (.cons (sameShape_shift z b) (forall₂_sameShape post))) ?_
  intro i
  suffices h : realPositionExponent (pre ++ [shiftBlock z b] ++ post) i =
      realPositionExponent (pre ++ [b] ++ post) i +
        z * (if realRank pre ≤ (i : ℕ) ∧ (i : ℕ) < realRank pre + b.rank then 1 else 0) by
    simpa only [List.append_assoc, List.singleton_append] using h
  by_cases hi : realRank pre ≤ (i : ℕ) ∧ (i : ℕ) < realRank pre + b.rank
  · let j := (i : ℕ) - realRank pre
    have hj : j < b.rank := by dsimp [j]; omega
    have hi' : (i : ℕ) = realRank pre + j := by dsimp [j]; omega
    have hmid (d : RealBlock) (hd : j < realRank [d]) :
        realPositionExponent (pre ++ [d] ++ post) i = realPositionExponent [d] j :=
      (congrArg (realPositionExponent (pre ++ [d] ++ post)) hi').trans
        (RealBlockPosition.realPositionExponent_mid pre [d] post hd)
    rw [ite_eq_left hi, mul_one, hmid b (by rwa [realRank_singleton]),
      hmid (shiftBlock z b) (by rwa [realRank_singleton, shiftBlock_rank])]
    exact singleton_shift_exponent z b j hj
  · have hnot : (i : ℕ) < realRank pre ∨ realRank pre + realRank [b] ≤ (i : ℕ) := by
      rw [realRank_singleton]
      omega
    rw [ite_eq_right hi, mul_zero, add_zero]
    exact (RealBlockPosition.realPositionExponent_of_not_mid
      (pre := pre) (post := post) (ws := [b]) (ws' := [shiftBlock z b])
      (by rw [realRank_singleton, realRank_singleton, shiftBlock_rank]) hnot).symm

end Langlands.Archimedean.RealExponentDeformation
