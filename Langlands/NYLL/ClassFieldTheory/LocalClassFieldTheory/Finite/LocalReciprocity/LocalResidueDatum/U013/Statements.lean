/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 14 November 2026:
State only the theorem M249.013 (lines 235–249) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709, without its proof, as the
closed proposition localBaseResidueEquivDecompositionResidue_algebraMapStatement.
The section variable K and its instance binders (lines 45–46) become leading
universal binders, followed by the theorem's own binder x. Add the
Langlands.NYLL namespace prefix, also in the opened namespaces, and the suffix
Statement. Import the Library modules that publish
localBaseResidueEquivDecompositionResidue, localSeparableValuationSubring_pullback
and the Algebra instance from the decomposition residue field to the selected
residue field, instead of the source imports. Omit the noncomputable section,
the open lines this statement does not need and all other declarations. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields

/-!
# Naturality of the base-residue comparison: target

A closed proposition about a nonarchimedean local field `K`: the comparison
`localBaseResidueEquivDecompositionResidue K` between the residue field of
`K` and the decomposition residue field `κ`, followed by the inclusion of `κ`
into the residue field `λ` of the chosen valuation ring of
`SeparableClosure K`, is the literal reduction of an integral element of `K`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- Closed target for NYLL M249.013
`localBaseResidueEquivDecompositionResidue_algebraMap`: naturality of the
base-residue comparison with the literal reduction map into the selected
residue field. -/
def localBaseResidueEquivDecompositionResidue_algebraMapStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (localCompleteDVF K).valuationSubring),
    algebraMap
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue (localCompleteDVF K).valuationSubring x)) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨algebraMap K (SeparableClosure K) (x : K),
          (localSeparableValuationSubring_pullback K (x : K)).2
            x.property⟩ : localSeparableValuationSubring K)

end Langlands.NYLL.LocalClassFieldTheory
