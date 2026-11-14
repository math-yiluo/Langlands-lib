/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Absolute.Definitions

/-!
# Finite local reciprocity: the Frobenius image in a residue algebraic closure (data)

Modified by Worker 46: extract the data command M236.012 of the pinned NYLL
`ResidueAlgebraicClosureDegree` source and prefix the namespace with
`Langlands.NYLL`. The source's private instances M236.002
(`IsAlgClosure k Omega`), M236.003 (`IsGalois k Omega`) and M236.004
(`T2Space (Omega ≃ₐ[k] Omega)`) are not declared: their values are supplied by
inlining `haveI`s in the body, so no instance is added. M236.003 is built as
`{}` from the local `IsAlgClosure` instance and M236.004 is Mathlib's
`krullTopology_t2`. The source imports of NYLL modules are replaced by the
published `Langlands.NYLL` port of `residueAbsoluteFrobenius`. The source's
`variable` blocks, universes, type and noncomputable status are retained. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

/-- The compact image of the intrinsic Frobenius homomorphism.

The instances of the source's private `residueAlgebraicClosureIsAlgClosure`,
`residueAlgebraicClosureIsGalois` and `residueAlgebraicClosureGaloisT2` are
supplied in place. -/
noncomputable def residueAbsoluteFrobeniusRangeIn :
    ClosedSubgroup (Omega ≃ₐ[k] Omega) :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  haveI : T2Space (Omega ≃ₐ[k] Omega) := krullTopology_t2
  { toSubgroup := (residueAbsoluteFrobenius k Omega).toMonoidHom.range
    isClosed' := by
      change IsClosed (Set.range (residueAbsoluteFrobenius k Omega))
      exact (isCompact_range
        (residueAbsoluteFrobenius k Omega).continuous_toFun).isClosed }

end
end Langlands.NYLL.LocalClassFieldTheory
