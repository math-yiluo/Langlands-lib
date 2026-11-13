/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.Definitions

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension (initial data)

Modified by Worker 123: extract the data command M168.001 of the pinned NYLL
`ResidueAbsoluteFrobenius` source and prefix the namespace with
`Langlands.NYLL`. The source import of the NYLL `FiniteResidueFrobenius` module
is replaced by the published `Langlands.NYLL` port of its definitions. The
source's `variable` block, universes, `open` commands, type, body and
noncomputable section are retained. The later source data commands M168.002,
M168.003 and M168.005, whose bodies need the proof of M167.018, are not part of
this module. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The finite Frobenius action on an intermediate field, with finiteness
derived from finite-dimensionality over the finite base. -/
def finiteResidueFrobeniusIntermediate
    (E : FiniteGaloisIntermediateField k Omega) :
    ZHatMul →ₜ* (E ≃ₐ[k] E) := by
  letI : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat k E

end
end Langlands.NYLL.LocalClassFieldTheory
