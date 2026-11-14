/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Frobenius.Definitions

/-!
# Finite local reciprocity: bijectivity of Frobenius on a residue algebraic closure (targets)

Modified by Worker 46: replace the source theorems M236.010, M236.013,
M236.014 and M236.015 of the pinned NYLL `ResidueAlgebraicClosureDegree`
source by Prop-valued `Statement` definitions in the `Langlands.NYLL`
namespace, under the source's `variable` blocks so that every target keeps the
source theorem's complete parameter telescope and universes. The source's
private instances M236.002 (`IsAlgClosure k Omega`) and M236.003
(`IsGalois k Omega`), which the source uses to apply `residueAbsoluteFrobenius`,
are not declared: in the targets of M236.010 and M236.015 their values are
supplied by inlining `haveI`s, M236.003 being built as `{}` from the local
`IsAlgClosure` instance. Source proofs are omitted. See the paired Markdown and
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

/-- Target of M236.010: the canonical Frobenius homomorphism
`ZHatMul →ₜ* Gal(Omega/k)` on any algebraic closure of a finite field is
injective. -/
def residueAbsoluteFrobenius_isAlgClosure_injectiveStatement : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  Function.Injective (residueAbsoluteFrobenius k Omega)

/-- Target of M236.013: the compact Frobenius image fixes precisely the finite
base field. -/
def fixedField_residueAbsoluteFrobeniusRangeInStatement : Prop :=
  IntermediateField.fixedField
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥

/-- Target of M236.014: the intrinsic Frobenius image is the whole residue
absolute Galois group. -/
def residueAbsoluteFrobeniusRangeIn_eq_topStatement : Prop :=
  (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤

/-- Target of M236.015: the canonical Frobenius homomorphism on any algebraic
closure of a finite field is surjective. -/
def residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  Function.Surjective (residueAbsoluteFrobenius k Omega)

end
end Langlands.NYLL.LocalClassFieldTheory
