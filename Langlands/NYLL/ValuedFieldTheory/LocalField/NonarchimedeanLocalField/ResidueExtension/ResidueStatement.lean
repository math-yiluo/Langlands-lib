/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 252, 13 November 2026:
Extract M138.007, source lines 88–96, from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued definition.
Prefix the namespace with Langlands.NYLL and append Statement to the name;
preserve the universe, complete telescope and equality. Omit the proof and
simp attribute and reduce imports to the two Mathlib dependencies below.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Residue compatibility of a valuation extension: statement

The exact proposition target of NYLL M138.007.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field algebra map commutes with reduction of valuation-ring elements. -/
def residueField_algebraMap_residueStatement (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) : Prop :=
  algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
    IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)

end

end Langlands.NYLL.LocalFieldTheory
