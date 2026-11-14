/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13 November 2026 UTC:
Extract the definition M237.004, valuationSubringComapResidueMap (source
lines 130-137), from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace by
Langlands.NYLL. The body is the source's; its local instance is the
published M237.003 theorem valuationSubringComapMap_isLocalHom. Import the
published U003 proof module instead of the source's imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.U003.Proofs

/-!
# The residue-field map of a pulled-back valuation subring

Definition M237.004: the ring homomorphism of residue fields induced by the
local map `valuationSubringComapMap` from the pullback of a valuation subring.
See the paired Markdown for the source map and the modification record.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- The residue-field embedding induced by pullback of a valuation ring. -/
noncomputable def valuationSubringComapResidueMap
    (A : ValuationSubring Omega) :
    IsLocalRing.ResidueField (A.comap (algebraMap F Omega)) →+*
      IsLocalRing.ResidueField A := by
  letI : IsLocalHom (valuationSubringComapMap (F := F) A) :=
    valuationSubringComapMap_isLocalHom (F := F) A
  exact IsLocalRing.ResidueField.map (valuationSubringComapMap (F := F) A)

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
