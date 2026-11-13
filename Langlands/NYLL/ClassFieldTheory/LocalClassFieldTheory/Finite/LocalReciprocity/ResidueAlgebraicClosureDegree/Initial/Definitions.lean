/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite local reciprocity: finite subextensions of a residue algebraic closure (data)

Modified by Worker 123: extract the data commands M236.005–M236.008 of the
pinned NYLL `ResidueAlgebraicClosureDegree` source and prefix the namespace with
`Langlands.NYLL`. The source's private instance M236.001
(`Fact (ringChar k).Prime`) is not declared: its value
`⟨CharP.char_is_prime k (ringChar k)⟩` is supplied by an inlining `haveI` in
each type and body that needs it, so no instance is added. The private
instances M236.002–M236.004 are not used by these commands. The source imports
of NYLL modules are replaced by the Mathlib modules these commands use, and the
`open` of the NYLL namespace `RamificationTheory.Field.absoluteGaloisGroup`
(unused here) is dropped. The source's `variable` blocks, universes, bodies and
noncomputable status are retained. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Embed the degree-`n` finite extension of `k` into the given residue
algebraic closure.  This choice is used only to prove that all profinite
coordinates are detected.

The characteristic-prime instance of the source's private
`finiteResidueBaseRingCharPrime` is supplied in place. -/
noncomputable def finiteResidueExtensionEmbeddingInto
    (n : ℕ) [NeZero n] :
    haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
    FiniteField.Extension k (ringChar k) n →ₐ[k] Omega := by
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  letI : Module.IsTorsionFree k Omega :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap k Omega).injective
  exact IsAlgClosed.lift (R := k)
    (S := FiniteField.Extension k (ringChar k) n) (M := Omega)

/-- The image of the degree-`n` finite extension in the given residue
algebraic closure.

The characteristic-prime instance of the source's private
`finiteResidueBaseRingCharPrime` is supplied in place. -/
noncomputable def finiteResidueIntermediateFieldIn
    (n : ℕ) [NeZero n] : IntermediateField k Omega :=
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  (⊤ : IntermediateField k
      (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbeddingInto k Omega n)

/-- The model finite field is canonically isomorphic to its embedded image.

The characteristic-prime instance of the source's private
`finiteResidueBaseRingCharPrime` is supplied in place. -/
noncomputable def finiteResidueExtensionEquivIntermediateIn
    (n : ℕ) [NeZero n] :
    haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateFieldIn k Omega n :=
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤
      (finiteResidueExtensionEmbeddingInto k Omega n))

/-- An actual degree-`n` finite Galois intermediate field in any residue
algebraic closure.

The characteristic-prime instance of the source's private
`finiteResidueBaseRingCharPrime` is supplied in place. -/
noncomputable def finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] : FiniteGaloisIntermediateField k Omega :=
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  { toIntermediateField := finiteResidueIntermediateFieldIn k Omega n
    finiteDimensional := Module.Finite.equiv
      (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv
    isGalois := IsGalois.of_algEquiv
      (finiteResidueExtensionEquivIntermediateIn k Omega n) }

end
end Langlands.NYLL.LocalClassFieldTheory
