/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: the type of the source theorem
LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMap
(inventory M252.003) becomes the proposition target
Langlands.NYLL.LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement,
with the source binders as its parameters. The proof is omitted (it is a
separate proof unit). The namespace is prefixed with Langlands.NYLL; the NYLL
imports are replaced by the published modules defining
residueFieldEquivDecompositionResidueOfEqTop and the residue-field instances;
the opens of the unused namespaces CyclicCohomology, ClassFormation,
LocalFieldTheory and ValuationTheory and the unused
`open scoped ValuativeRel` are omitted. All other source declarations are
omitted. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields

/-!
# Naturality of the literal-to-intrinsic residue equivalence: proposition target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`,
lines 22–34 (namespace, opens, universes) and 103–119 (inventory M252.003,
docstring and type).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory

noncomputable section

open HilbertRamification.ValuationSubring

universe u v

/-- Naturality of the preceding residue equivalence with reduction into the
selected residue field. -/
def residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) : Prop :=
    algebraMap (decompositionResidueField F A) (selectedResidueField A)
        (residueFieldEquivDecompositionResidueOfEqTop A C hC hA
          (IsLocalRing.residue C x)) =
      IsLocalRing.residue A
        (⟨algebraMap F Omega (x : F), by
          have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
            rw [hC]
            exact x.property
          exact hx⟩ : A)

end

end Langlands.NYLL.LocalClassFieldTheory
