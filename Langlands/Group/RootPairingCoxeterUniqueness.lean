import Langlands.Group.RootPairingSigns
import Langlands.Group.CoxeterSimpleInjective

/-! # The root-sign length law determines simple generators -/

noncomputable section

namespace Langlands.Group.RootPairingSigns

open IsAddIndecomposable

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] (f : Module.Dual R M)

/-- The right-length law using the actual simple-root labels. -/
def RootSignLengthLaw {C : CoxeterMatrix (baseOf P.root (f : M →+ R))}
    (cs : CoxeterSystem C P.weylGroup) : Prop :=
  ∀ w b, cs.length w < cs.length (w * cs.simple b) ↔ 0 < f (w • P.root b)

/-- A Coxeter system with the root-sign length law has the actual root reflections
as its labelled simple generators. -/
theorem simple_eq_of_rootSignLengthLaw (hf : ∀ i, f (P.root i) ≠ 0)
    {C : CoxeterMatrix (baseOf P.root (f : M →+ R))}
    (cs : CoxeterSystem C P.weylGroup) (hLength : RootSignLengthLaw P f cs)
    (a : baseOf P.root (f : M →+ R)) :
    cs.simple a = RootPairing.weylGroup.ofIdx P a := by
  classical
  let t := RootPairing.weylGroup.ofIdx P a
  have hnonzero (w : P.weylGroup) (r : ι) : f (w • P.root r) ≠ 0 := by
    rw [P.weylGroup_apply_root]
    exact hf _
  have hsneg : f (cs.simple a • P.root a) < 0 := by
    have hno : ¬0 < f (cs.simple a • P.root a) :=
      (hLength (cs.simple a) a).not.mp (by simp [cs.simple_mul_simple_self])
    exact lt_of_le_of_ne (not_lt.mp hno) (hnonzero _ _)
  have htneg : f (t • P.root a) < 0 := by
    change f (P.reflection a (P.root a)) < 0
    rw [P.reflection_apply_self, map_neg]
    exact neg_neg_of_pos (baseOf_subset_pos P.root (f : M →+ R) a.property)
  have htdesc : cs.length (t * cs.simple a) < cs.length t := by
    have hno := (hLength t a).not.mpr (not_lt_of_gt htneg)
    have hne := cs.length_mul_simple_ne t a
    omega
  have hpos : ∀ b : baseOf P.root (f : M →+ R),
      0 < f ((t * cs.simple a) • P.root b) := by
    intro b
    by_cases hab : b = a
    · subst b
      apply (hLength (t * cs.simple a) a).mp
      simpa only [cs.simple_mul_simple_cancel_right] using htdesc
    · have hprodne : cs.simple a * cs.simple b ≠ 1 := by
        intro heq
        have hs := congrArg (fun w => w * cs.simple b) heq
        simp only [cs.simple_mul_simple_cancel_right, one_mul] at hs
        exact hab (RelativeWeylIndexing.simple_injective cs hs).symm
      have htwo : cs.length (cs.simple a * cs.simple b) = 2 := by
        have hne : cs.length (cs.simple a * cs.simple b) ≠ 0 :=
          fun h => hprodne (cs.length_eq_zero_iff.mp h)
        rcases cs.length_mul_simple (cs.simple a) b with h | h <;>
          simp only [cs.length_simple] at h <;> omega
      have hspos : 0 < f (cs.simple a • P.root b) := by
        apply (hLength (cs.simple a) b).mp
        rw [cs.length_simple, htwo]
        omega
      by_contra hno
      have hneg : f ((t * cs.simple a) • P.root b) < 0 :=
        lt_of_le_of_ne (not_lt.mp hno) (hnonzero _ _)
      rw [mul_smul] at hneg
      change f (P.reflection a (cs.simple a • P.root b)) < 0 at hneg
      rw [P.weylGroup_apply_root] at hneg hspos
      obtain ⟨n, hn⟩ := eq_nsmul_of_reflection_neg P f hf a.property hspos hneg
      have hn' : cs.simple a • P.root b = n • P.root a := by
        rwa [P.weylGroup_apply_root]
      have hback := congrArg (P.weylGroupRootRep (cs.simple a)) hn'
      change cs.simple a • (cs.simple a • P.root b) =
        cs.simple a • (n • P.root a) at hback
      have hcomm : cs.simple a • (n • P.root a) = n • (cs.simple a • P.root a) :=
        map_nsmul (P.weylGroupRootRep (cs.simple a)) _ _
      rw [← mul_smul, cs.simple_mul_simple_self, one_smul, hcomm] at hback
      have hle : f (P.root b) ≤ 0 := by
        rw [hback, map_nsmul, nsmul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_lt hsneg)
      exact (not_le_of_gt (baseOf_subset_pos P.root (f : M →+ R) b.property)) hle
  obtain ⟨_, C₀, cs₀, hs₀, _, hl₀⟩ :=
    Langlands.Group.rootPairingWeylCoxeterStatement_proof ι R M N P f hf
  have hu : t * cs.simple a = 1 := by
    by_contra hne
    obtain ⟨b, hb⟩ := cs₀.exists_rightDescent_of_ne_one hne
    have hinc := (hl₀ (t * cs.simple a) b).mpr (hpos b)
    exact (not_lt_of_gt hinc) hb
  have heq := congrArg (fun w => w * cs.simple a) hu
  simpa only [cs.simple_mul_simple_cancel_right, one_mul] using heq.symm

end Langlands.Group.RootPairingSigns
