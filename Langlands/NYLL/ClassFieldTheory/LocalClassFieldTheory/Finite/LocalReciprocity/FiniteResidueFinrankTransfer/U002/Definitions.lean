/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the source definition
LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop
(inventory M252.002) as
Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop.
The universes, binders, type and body are unchanged. The namespace is
prefixed with Langlands.NYLL; the NYLL imports are replaced by the published
modules defining valuationSubringEquivDecompositionFieldOfEqTop and
decompositionFieldResidueEquiv; the opens of the unused namespaces
CyclicCohomology, ClassFormation, LocalFieldTheory and ValuationTheory and
the unused `open scoped ValuativeRel` are omitted. All other source
declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison

/-!
# Literal and intrinsic residue fields when the decomposition group is everything

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`,
lines 22–34 (namespace, opens, universes) and 90–101 (inventory M252.002).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory

noncomputable section

open HilbertRamification.ValuationSubring

universe u v

/-- The corresponding equivalence between literal and intrinsic residue
fields. -/
noncomputable def residueFieldEquivDecompositionResidueOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    IsLocalRing.ResidueField C ≃+* decompositionResidueField F A :=
  (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringEquivDecompositionFieldOfEqTop A C hC hA)).trans
    (decompositionFieldResidueEquiv (K := F) A)

end

end Langlands.NYLL.LocalClassFieldTheory
