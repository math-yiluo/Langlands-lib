/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M084.001
(abstractReciprocity_fixedCombination_of_commute) from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published FixedCombination Statements
module. Keep the noncomputable section and the docstring; omit the unused
`open KummerTheory`, `open CyclicCohomology`, and the section variable line
for `G` with its comment, which this theorem does not use. State the theorem
as the published Statement applied to the source parameters. The proof is
unchanged. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.FixedCombination.Statements

/-!
# The fixed corrected combination

The proof that, for commuting group elements acting compatibly on a
coboundary, the standard corrected combination is fixed by the first
element.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

/-- If two commuting group elements act compatibly on a coboundary, the
standard corrected combination is fixed by the first element. -/
theorem abstractReciprocity_fixedCombination_of_commute
    {Q : IntegralRepGroupType} [Group Q] (B : Rep ℤ Q)
    (g t : Q) (hcomm : Commute g t) (c b a : B.V)
    (htc : B.ρ t c = c)
    (hgb : B.ρ g b = B.ρ t b)
    (hbc : b - c = B.ρ g a - a) :
    abstractReciprocity_fixedCombination_of_commuteStatement
      B g t hcomm c b a htc hgb hbc := by
  have hcommAction : B.ρ g (B.ρ t a) = B.ρ t (B.ρ g a) := by
    calc
      B.ρ g (B.ρ t a) = B.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = B.ρ (t * g) a := by rw [hcomm.eq]
      _ = B.ρ t (B.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + B.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (B.ρ g a - a) + c := by rw [hbc]
      _ = c + B.ρ g a - a := by abel
  have htbc := congrArg (fun z : B.V ↦ B.ρ t z) hbc
  have htbc' : B.ρ t b - c = B.ρ t (B.ρ g a) - B.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : B.ρ t b = c + B.ρ t (B.ρ g a) - B.ρ t a := by
    calc
      B.ρ t b = (B.ρ t b - c) + c := by abel
      _ = (B.ρ t (B.ρ g a) - B.ρ t a) + c := by rw [htbc']
      _ = c + B.ρ t (B.ρ g a) - B.ρ t a := by abel
  calc
    B.ρ g (b + a - B.ρ t a) =
        B.ρ g b + B.ρ g a - B.ρ g (B.ρ t a) := by
      simp only [map_add, map_sub]
    _ = B.ρ t b + B.ρ g a - B.ρ t (B.ρ g a) := by
      rw [hgb, hcommAction]
    _ = c + B.ρ g a - B.ρ t a := by rw [htb]; abel
    _ = b + a - B.ρ t a := by rw [hb]; abel

end Langlands.NYLL.ClassFormation

end
