/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 215, 2026-11-14: adaptation of NYLL M243.025/.029/.030 for
Task 5836 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Namespace prefixed with Langlands.NYLL; selected source rows extracted
into a focused module with published Library imports.
See the paired Markdown for the source lines and all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueAction

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- NYLL M243.025: reduction intertwines the valuation-ring and residue actions. -/
abbrev decompositionGroupResidueAction_residueStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L)
    (sigma : decompositionGroup K A) (x : A),
    decompositionGroupResidueAction (K := K) A sigma
        (IsLocalRing.residue A x) =
      IsLocalRing.residue A (sigma • x)

/-- NYLL M243.029: the residue action is onto, also for infinite Galois extensions. -/
def decompositionGroupResidueAction_surjectiveStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (A : _root_.ValuationSubring L),
    Function.Surjective (decompositionGroupResidueAction (K := K) A)

/-- NYLL M243.030: the actual residue extension is normal. -/
abbrev decompositionResidueExtension_normalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (A : _root_.ValuationSubring L),
    Normal (decompositionResidueField K A) (selectedResidueField A)

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
