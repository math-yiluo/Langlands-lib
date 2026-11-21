import Langlands.Representation.Archimedean.ComplexUnitaryStandardConjugation

/-! Adjacent pairs in a parameter list preserved by Hermitian duality. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexUnitary

open Langlands.LocalFactor.Archimedean

/-- A fixed character or a pair of Hermitian-dual characters, with the positive exponent first. -/
inductive ParameterBlock where
  | single (d : ComplexCharacterData) (h : d.exponent.re = 0)
  | pair (d : ComplexCharacterData) (h : 0 < d.exponent.re)

/-- The inducing characters of a block, in the order used for the intertwining integral. -/
def ParameterBlock.data : ParameterBlock → List ComplexCharacterData
  | .single d _ => [d]
  | .pair d _ => [d, hermitianData d]

@[simp] theorem ParameterBlock.single_map (d : ComplexCharacterData) (h : d.exponent.re = 0) :
    (ParameterBlock.single d h).data.map hermitianData = [d] := by
  simp [ParameterBlock.data, (hermitianData_eq_self_iff d).2 h]

@[simp] theorem ParameterBlock.pair_map (d : ComplexCharacterData) (h : 0 < d.exponent.re) :
    (ParameterBlock.pair d h).data.map hermitianData = [hermitianData d, d] := by
  simp [ParameterBlock.data]

/-- A Hermitian-dual-stable list can be permuted into fixed characters and adjacent dual pairs.
The statement retains multiplicities. -/
theorem exists_parameterBlocks (ds : List ComplexCharacterData)
    (h : ds.Perm (ds.map hermitianData)) :
    ∃ bs : List ParameterBlock, ds.Perm (bs.flatMap ParameterBlock.data) := by
  generalize hl : ds.length = l
  induction l using Nat.strong_induction_on generalizing ds with
  | h l ih =>
   cases ds with
   | nil => exact ⟨[], List.Perm.nil⟩
   | cons d ds =>
    by_cases hz : d.exponent.re = 0
    · have hd : hermitianData d = d := (hermitianData_eq_self_iff d).2 hz
      have ht : ds.Perm (ds.map hermitianData) :=
        List.Perm.cons_inv (by simpa only [List.map_cons, hd] using h)
      have hlt : ds.length < l := by simp only [List.length_cons] at hl; omega
      obtain ⟨bs, hbs⟩ := ih ds.length hlt ds ht rfl
      exact ⟨.single d hz :: bs, hbs.cons d⟩
    · have hd : hermitianData d ≠ d := fun e => hz ((hermitianData_eq_self_iff d).1 e)
      have hm : hermitianData d ∈ ds := by
        have hm' := h.mem_iff.mpr (List.mem_map.mpr ⟨d, List.mem_cons_self, rfl⟩)
        exact (List.mem_cons.mp hm').resolve_left hd
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
      have hp : (d :: pre ++ hermitianData d :: post).Perm (d :: hermitianData d :: (pre ++ post)) :=
        List.Perm.cons _ List.perm_middle
      have hpair : (d :: hermitianData d :: (pre ++ post)).Perm
          (hermitianData d :: d :: (pre ++ post).map hermitianData) := by
        simpa only [List.map_cons, hermitianData_involutive] using
          hp.symm.trans (h.trans (hp.map hermitianData))
      have ht : (pre ++ post).Perm ((pre ++ post).map hermitianData) :=
        List.Perm.cons_inv (List.Perm.cons_inv (hpair.trans (List.Perm.swap _ _ _)))
      have hlt : (pre ++ post).length < l := by
        simp only [List.length_append, List.length_cons] at hl ⊢
        omega
      obtain ⟨bs, hbs⟩ := ih (pre ++ post).length hlt (pre ++ post) ht rfl
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · have hpos' : 0 < (hermitianData d).exponent.re := by simp [hneg]
        refine ⟨.pair (hermitianData d) hpos' :: bs, ?_⟩
        simpa [ParameterBlock.data] using hp.trans
          ((List.Perm.swap (hermitianData d) d _).trans ((hbs.cons d).cons (hermitianData d)))
      · exact ⟨.pair d hpos :: bs, hp.trans ((hbs.cons (hermitianData d)).cons d)⟩

end Langlands.Archimedean.ComplexUnitary
