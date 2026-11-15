/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.ExponentEquiv.Definitions

/-!
# Finite local reciprocity: finite coordinates of the intrinsic residue degree (targets)

Modified by Worker 46: state the theorem M236.022 of the pinned NYLL
`ResidueAlgebraicClosureDegree` source as the Prop-valued target
`finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement` in the
`Langlands.NYLL` namespace, under the source's `variable` blocks. The theorem's
arguments `sigma` and `E` become explicit arguments of the target, and its
statement, including the local `Finite E` instance, is kept. The source imports
of NYLL modules are replaced by the `Langlands.NYLL` modules of
`residueAbsoluteDegreeIn` and `finiteResidueFrobeniusExponentEquiv`. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Target of M236.022: finite-coordinate compatibility for the intrinsic
residue degree. The finite Frobenius coordinate of the restriction of `sigma`
to a finite Galois subextension `E` is the reduction modulo `[E : k]` of the
intrinsic residue degree of `sigma`. -/
def finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement
    (sigma : Omega ≃ₐ[k] Omega)
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  letI : Finite E := Module.finite_of_finite k
  (finiteResidueFrobeniusExponentEquiv k E).symm
      (AlgEquiv.restrictNormalHom E sigma) =
    Multiplicative.ofAdd
      (zHatReduction (Module.finrank k E) Module.finrank_pos
        (residueAbsoluteDegreeIn k Omega sigma).toAdd)

end
end Langlands.NYLL.LocalClassFieldTheory
