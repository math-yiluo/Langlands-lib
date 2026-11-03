import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-! # Chamber alignment in a finite rational root system -/

noncomputable section

namespace Langlands.LinearAlgebra.RootPairingChambers

variable {J M N : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] (P : RootPairing J ℚ M N)

/-- A covector is regular if every root evaluates nontrivially on it. -/
def Regular (f : N) : Prop :=
  ∀ i, P.root' i f ≠ 0

/-- Two covectors determine the same positive root set. -/
def SameChamber (f g : N) : Prop :=
  ∀ i, 0 < P.root' i f ↔ 0 < P.root' i g

private theorem finite_aut [Finite J] [P.IsRootSystem] : Finite P.Aut := by
  apply Finite.of_injective (RootPairing.Equiv.indexHom P)
  intro a b hab
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (RootPairing.IsRootSystem.span_root_eq_top (P := P))
  intro i
  change a.toHom.weightMap (P.root i) = b.toHom.weightMap (P.root i)
  rw [RootPairing.Hom.root_weightMap_apply, RootPairing.Hom.root_weightMap_apply]
  exact congrArg P.root (congrFun (congrArg Equiv.toFun hab) i)

variable [Fintype J]

/-- Each coroot has strictly positive squared norm for the canonical form. -/
theorem corootForm_coroot_pos (i : J) :
    0 < P.CorootForm (P.coroot i) (P.coroot i) := by
  rw [P.corootForm_apply_apply]
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i, Finset.mem_univ _, by simp⟩

/-- The canonical form pairs with a coroot by a positive multiple of root evaluation. -/
theorem two_mul_corootForm_coroot (i : J) (f : N) :
    2 * P.CorootForm f (P.coroot i) =
      P.CorootForm (P.coroot i) (P.coroot i) * P.root' i f := by
  have h := congrArg (fun x : M => P.toLinearMap x f)
    (P.corootForm_self_smul_root i)
  have hs : P.CorootForm (P.coroot i) f = P.CorootForm f (P.coroot i) :=
    P.flip.rootForm_symmetric.eq _ _
  simp only [map_smul, map_nsmul, LinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  rw [P.toLinearMap_apply_CoPolarization, hs] at h
  exact h.symm

/-- A maximum of the canonical pairing on the finite Weyl orbit has no opposite
root evaluations, including when either covector is singular. -/
theorem exists_weylGroup_nonneg [P.IsRootSystem] (f g : N) :
    ∃ w : P.weylGroup, ∀ i,
      0 ≤ P.root' i f * P.root' i (w.val.coweightEquiv g) := by
  have : Finite P.Aut := finite_aut P
  obtain ⟨w, hw⟩ := Finite.exists_max
    (fun w : P.weylGroup => P.CorootForm f (w.val.coweightEquiv g))
  refine ⟨w, fun i => ?_⟩
  have hi := hw (w * RootPairing.weylGroup.ofIdx P i)
  change P.CorootForm f (P.coreflection i (w.val.coweightEquiv g)) ≤
    P.CorootForm f (w.val.coweightEquiv g) at hi
  rw [P.coreflection_apply, map_sub, map_smul, smul_eq_mul] at hi
  have hn := corootForm_coroot_pos P i
  have he := two_mul_corootForm_coroot P i f
  have hmul : 0 ≤ P.root' i (w.val.coweightEquiv g) *
      P.CorootForm f (P.coroot i) := by linarith
  have hprod : 0 ≤ P.CorootForm (P.coroot i) (P.coroot i) *
      (P.root' i f * P.root' i (w.val.coweightEquiv g)) := by
    calc
      0 ≤ 2 * (P.root' i (w.val.coweightEquiv g) *
        P.CorootForm f (P.coroot i)) := mul_nonneg (by norm_num) hmul
      _ = P.root' i (w.val.coweightEquiv g) *
        (2 * P.CorootForm f (P.coroot i)) := by ring
      _ = _ := by rw [he]; ring
  exact nonneg_of_mul_nonneg_right hprod hn

omit [Fintype J] in
/-- The contravariant coweight action preserves root-regularity. -/
theorem regular_coweightEquiv {g : N} (hg : Regular P g) (w : P.Aut) :
    Regular P (w.coweightEquiv g) := by
  intro i
  have h := w.root'_coweightEquiv i (w.coweightEquiv g)
  simp only [LinearEquiv.symm_apply_apply] at h
  exact h ▸ hg (w.indexEquiv i)

/-- Every two regular covectors have Weyl translates with the same root signs. -/
theorem exists_weylGroup_sameChamber [P.IsRootSystem] {f g : N}
    (hf : Regular P f) (hg : Regular P g) :
    ∃ w : P.weylGroup, SameChamber P f (w.val.coweightEquiv g) := by
  obtain ⟨w, hw⟩ := exists_weylGroup_nonneg P f g
  refine ⟨w, fun i => ?_⟩
  have hg' := regular_coweightEquiv P hg w.val i
  have hpos : 0 < P.root' i f * P.root' i (w.val.coweightEquiv g) :=
    lt_of_le_of_ne (hw i) (Ne.symm (mul_ne_zero (hf i) hg'))
  rcases mul_pos_iff.mp hpos with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false (not_lt.mpr h.1.le) (not_lt.mpr h.2.le)

end Langlands.LinearAlgebra.RootPairingChambers
