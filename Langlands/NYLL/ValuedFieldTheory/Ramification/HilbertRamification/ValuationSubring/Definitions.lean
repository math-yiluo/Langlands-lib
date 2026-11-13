/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 215, 2026-11-13: extract M239.001–003 and M239.011
from commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL and reduce imports to the two Mathlib dependencies below.
The four abbreviations, universe parameters and field/algebra binders are unchanged.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! # Valuation-subring decomposition, inertia and fixed-field aliases -/

noncomputable section

universe u v

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- finite Galois ramification theory:
the decomposition group of a valuation subring. -/
abbrev decompositionGroup (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the inertia group of a valuation subring. -/
abbrev inertiaGroup (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field. -/
abbrev residueAction (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group. -/
abbrev decompositionField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)


end Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
