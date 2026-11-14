/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U007.Proofs

/-!
# Finite local reciprocity: the finite residue Frobenius coordinate equivalence

Modified by Worker 123: extract the data command M167.008 of the pinned NYLL
`FiniteResidueFrobenius` source and prefix the namespace with `Langlands.NYLL`.
The source module is replaced by the published `Langlands.NYLL` proofs of
M167.006 and M167.007, which the body uses. The source's `variable` block,
universes, `open` command, type, body and noncomputable section are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- Canonical finite-level Frobenius coordinates. -/
def finiteResidueFrobeniusExponentEquiv :
    Multiplicative (ZMod (Module.finrank k L)) ≃* (L ≃ₐ[k] L) :=
  MulEquiv.ofBijective (finiteResidueFrobeniusExponentHom k L)
    ⟨finiteResidueFrobeniusExponentHom_injective k L,
      finiteResidueFrobeniusExponentHom_surjective k L⟩

end
end Langlands.NYLL.LocalClassFieldTheory
