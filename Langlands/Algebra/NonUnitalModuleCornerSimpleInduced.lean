import Langlands.Algebra.NonUnitalModuleCornerSimpleSubmodules

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction
open NonUnitalModuleIdempotentGenerated NonUnitalModuleCornerSimpleStatements
open NonUnitalModuleCornerInductionGenerated

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uM uW

variable {A : Type uA} [NonUnitalRing A]

/-- The fixed vectors lying in an original stable subgroup form a corner submodule. -/
def fixedSubmodule (e : Idempotent A) {M : Type uM}
    [AddCommGroup M] [NonUnitalModule A M] (S : NonUnitalSubmodule A M) :
    Submodule (Idempotent.Corner e) (FixedPart e M) where
  carrier := {z | z.val ∈ S}
  zero_mem' := S.toAddSubgroup.zero_mem
  add_mem' hx hy := S.toAddSubgroup.add_mem hx hy
  smul_mem' c _ hz := S.smul_mem' c.val hz

/-- Generation, vanishing annihilator and corner simplicity imply the stable-subgroup dichotomy. -/
theorem stable_dichotomy_of_corner (e : Idempotent A) (M : Type uM)
    [AddCommGroup M] [NonUnitalModule A M]
    (hg : IsGeneratedByIdempotent e M)
    (hz : ∀ m ∈ NonUnitalSubmodule.idempotentAnnihilator e M, m = 0)
    [IsSimpleModule (Idempotent.Corner e) (FixedPart e M)]
    (S : NonUnitalSubmodule A M) :
    (∀ x : S, x.val = 0) ∨ ∀ m : M, m ∈ S := by
  rcases eq_bot_or_eq_top (fixedSubmodule e S) with hb | ht
  · left
    intro x
    apply hz x.val
    intro a
    have hm : projection e (a • x.val) ∈ fixedSubmodule e S :=
      S.smul_mem' (e : A) (S.smul_mem' a x.property)
    rw [hb] at hm
    have hval := congrArg Subtype.val (show projection e (a • x.val) = 0 from hm)
    exact (mul_smul (e : A) a x.val).trans hval
  · right
    have hfixed : fixedPart e M ≤ S.toAddSubgroup := by
      intro m hm
      have h : (⟨m, hm⟩ : FixedPart e M) ∈ fixedSubmodule e S := by
        rw [ht]
        trivial
      exact h
    exact fun m => (aeM_le_iff e S).2 hfixed (hg m)

/-- A simple corner module induces a simple original annihilator quotient. -/
theorem simpleInducedQuotient : SimpleInducedQuotientStatement.{uA, uW} := by
  intro A _ hA e W _ _ hW
  let := hW
  let Q := (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj
    (nondegenerateObject hA e W)
  have hfixed : IsSimpleModule (Idempotent.Corner e) (FixedPart e Q.obj) :=
    (fixedQuotientEquivalence e W).isSimpleModule_iff.mp hW
  let := hfixed
  have hn : Nontrivial (FixedPart e Q.obj) :=
    IsSimpleModule.nontrivial (Idempotent.Corner e) (FixedPart e Q.obj)
  let := hn
  obtain ⟨z, hz⟩ := exists_fixed_ne_zero e Q.obj
  let : Nontrivial Q.obj := ⟨⟨z.val, 0, hz⟩⟩
  refine ⟨simple_of_stable_dichotomy hA Q ?_, hn⟩
  apply stable_dichotomy_of_corner e Q.obj
  · exact isGenerated_of_surjective e (annihilatorQuotientProjection e (Tensor e W))
      (annihilatorQuotientProjection_surjective e) (tensor_isGenerated e W)
  · exact IdempotentAnnihilatorComparisons.quotient_annihilator_eq_zero e (Tensor e W)

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
