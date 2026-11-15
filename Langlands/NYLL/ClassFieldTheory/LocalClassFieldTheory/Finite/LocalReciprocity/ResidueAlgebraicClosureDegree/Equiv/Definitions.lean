/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U015.Proofs

/-!
# Finite local reciprocity: the intrinsic residue degree (data)

Modified by Worker 46: extract the data commands M236.016 and M236.017 of the
pinned NYLL `ResidueAlgebraicClosureDegree` source and prefix the namespace
with `Langlands.NYLL`. The source's private instances M236.002
(`IsAlgClosure k Omega`), M236.003 (`IsGalois k Omega`) and M236.004
(`T2Space (Omega ≃ₐ[k] Omega)`) are not declared: their values are supplied by
inlining `haveI`s in the body of M236.016, so no instance is added. M236.003 is
built as `{}` from the local `IsAlgClosure` instance and M236.004 is Mathlib's
`krullTopology_t2`. The source's injectivity (M236.010) and surjectivity
(M236.015) theorems are the published `Langlands.NYLL` proofs of their
targets. The source imports of NYLL modules are replaced by those two proof
modules. The source's `variable` blocks, universes, types, bodies and
noncomputable status are otherwise retained. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

/-- Arithmetic Frobenius gives the canonical topological equivalence between
`ZHatMul` and the Galois group of any algebraic closure of a finite field
(M236.016).

The instances of the source's private `residueAlgebraicClosureIsAlgClosure`,
`residueAlgebraicClosureIsGalois` and `residueAlgebraicClosureGaloisT2` are
supplied in place. -/
noncomputable def residueAbsoluteFrobeniusEquivIn :
    ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega) :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  haveI : T2Space (Omega ≃ₐ[k] Omega) := krullTopology_t2
  { toMulEquiv := MulEquiv.ofBijective
      (residueAbsoluteFrobenius k Omega).toMonoidHom
      ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
        residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩
    continuous_toFun := (residueAbsoluteFrobenius k Omega).continuous_toFun
    continuous_invFun :=
      Continuous.continuous_symm_of_equiv_compact_to_t2
        (f := (MulEquiv.ofBijective
          (residueAbsoluteFrobenius k Omega).toMonoidHom
          ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
            residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩).toEquiv)
        (residueAbsoluteFrobenius k Omega).continuous_toFun }

/-- **Finite local reciprocity, intrinsic residue degree.** This is the inverse
of arithmetic Frobenius coordinates on the actual residue algebraic closure
(M236.017). -/
noncomputable def residueAbsoluteDegreeIn :
    (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (residueAbsoluteFrobeniusEquivIn k Omega).symm

end
end Langlands.NYLL.LocalClassFieldTheory
