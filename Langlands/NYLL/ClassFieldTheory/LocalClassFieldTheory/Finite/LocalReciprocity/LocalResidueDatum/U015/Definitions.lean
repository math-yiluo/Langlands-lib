/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract M249.015 (instance localDecompositionResidueFintype, lines 262–266)
from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespaces. In the source, the body
Fintype.ofFinite _ finds the Finite instance of the source instance
localDecompositionResidueFinite (M249.014, lines 252–260), whose proof is not
published. The body instead supplies that Finite fact by a local haveI,
proved by the source proof of lines 256–260, and then applies
Fintype.ofFinite _ as in the source. Import the Library module that
publishes localBaseResidueEquivDecompositionResidue instead of the source
imports. Omit the open lines this instance does not need and all other
declarations. The docstring and type are the source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions

/-!
# A finite enumeration of the local decomposition residue field

For a nonarchimedean local field `K`, the base residue field
`decompositionResidueField K (localSeparableValuationSubring K)` of the
chosen valuation ring of `SeparableClosure K` is finite. This module records
the resulting `Fintype` instance.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The finite local decomposition residue field has a canonical finite enumeration. -/
noncomputable instance localDecompositionResidueFintype :
    Fintype (decompositionResidueField K
      (localSeparableValuationSubring K)) :=
  -- M249.014 (source instance `localDecompositionResidueFinite`), inlined
  haveI : Finite (decompositionResidueField K
      (localSeparableValuationSubring K)) := by
    have : Finite (localCompleteDVF K).residueField := by
      change Finite 𝓀[K]
      infer_instance
    exact Finite.of_equiv (localCompleteDVF K).residueField
      (localBaseResidueEquivDecompositionResidue K).toEquiv
  Fintype.ofFinite _

end

end Langlands.NYLL.LocalClassFieldTheory
