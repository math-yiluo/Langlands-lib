/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 122, 15 November 2026, following the route that
Worker 85 checked:
Prove the published target of M252.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FiniteResidueFinrankTransfer.lean (theorem
residueFieldEquivDecompositionResidueOfEqTop_algebraMap, lines 103-120) at
fbd320cd8b1b06487c58227e92eb135794267709. The theorem keeps the source
binders and its universes u v; its type is the published proposition target
applied to those binders. The source proof `rfl` is kept unchanged. Add the
Langlands.NYLL namespace prefix, import the published target module instead
of the source imports, and omit the unused opens.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer.U003.Statements

/-!
# Naturality of the literal-to-intrinsic residue equivalence (NYLL M252.003)

Reducing `x ∈ C` in the residue field of `C`, transporting it by
`residueFieldEquivDecompositionResidueOfEqTop` to the intrinsic residue field
and mapping it into the selected residue field of `A` gives the residue class
of `x` viewed in `A`. Both sides unfold to the same residue class, so the
proof is `rfl`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory

noncomputable section

open HilbertRamification.ValuationSubring

universe u v

/-- Naturality of the preceding residue equivalence with reduction into the
selected residue field. -/
theorem residueFieldEquivDecompositionResidueOfEqTop_algebraMap
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) :
    residueFieldEquivDecompositionResidueOfEqTop_algebraMapStatement
      A C hC hA x := by
  rfl

end

end Langlands.NYLL.LocalClassFieldTheory
