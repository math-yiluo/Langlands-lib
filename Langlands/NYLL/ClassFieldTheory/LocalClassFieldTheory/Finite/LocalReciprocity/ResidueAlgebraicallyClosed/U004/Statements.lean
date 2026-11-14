/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13-14 November 2026 UTC:
Extract the signature of M237.006 (source lines 148-160) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace by
Langlands.NYLL and replace the source theorem by a Prop-valued definition
with the suffix Statement and the source's binders and proposition. The
target binds [IsPurelyInseparable F Omega] in its own signature, as the
source theorem does. The source proof is omitted. M237.005 (source lines
139-146) is not restated: it is covered by Mathlib's
IsLocalRing.ResidueField.map_residue with the published
valuationSubringComapMap_isLocalHom as local instance (see the paired
Markdown). Import the sibling U004 definition module and
Mathlib.FieldTheory.PurelyInseparable.Basic instead of the source's imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.U004.Definitions
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Target: residue fields of a purely inseparable extension

Prop-valued target for M237.006 (purely inseparable ambient extensions give
purely inseparable residue extensions). M237.005 is reused from Mathlib. See
the paired Markdown for the source map and the modification record. No proof
is asserted here.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- Target for M237.006: a purely inseparable extension remains purely
inseparable after passing to the residue fields of a valuation ring and its
pullback. -/
def valuationSubring_comap_residueField_isPurelyInseparableStatement
    [IsPurelyInseparable F Omega] (A : ValuationSubring Omega) : Prop :=
  letI : Algebra
      (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
      (IsLocalRing.ResidueField A) :=
    (valuationSubringComapResidueMap (F := F) A).toAlgebra
  IsPurelyInseparable
    (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
    (IsLocalRing.ResidueField A)

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
