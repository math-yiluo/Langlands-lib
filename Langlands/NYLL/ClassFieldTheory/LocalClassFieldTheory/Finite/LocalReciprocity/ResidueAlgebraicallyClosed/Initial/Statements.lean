/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13 November 2026 UTC:
Extract the signature of M237.003 (source lines 81-97) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace by
Langlands.NYLL and replace the source theorem by a Prop-valued definition
with the suffix Statement and the source's binders and proposition. The
source proof is omitted. M237.001 (source lines 29-77) is not adapted here:
the published Library theorem Langlands.LocalGalois.residue_isAlgClosed has
its exact signature and is reused by name (see the paired Markdown). Import
the sibling Initial definition of M237.002 instead of the source's imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.Initial.Definitions

/-!
# Target: the pulled-back valuation-ring map is local

Prop-valued target for M237.003: the ring map from the pulled-back valuation
subring to the ambient valuation subring is a local homomorphism. The source
theorem M237.001 is covered by the published
`Langlands.LocalGalois.residue_isAlgClosed` and is not duplicated. See the
paired Markdown for the source map and the modification record. No proof is
asserted here.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

/-! ## Residues under a purely inseparable ambient extension -/

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- Target for M237.003: pullback along a field embedding gives a local map
of valuation rings. -/
def valuationSubringComapMap_isLocalHomStatement (A : ValuationSubring Omega) : Prop :=
  IsLocalHom (valuationSubringComapMap (F := F) A)

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
