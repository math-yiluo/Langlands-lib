/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.Definitions

/-!
# Finite local reciprocity: finite residue Frobenius coordinates (targets)

Modified by Worker 123: replace the source theorems M167.004–007, M167.012–013
and M167.016–018 of the pinned NYLL `FiniteResidueFrobenius` source by
Prop-valued `Statement` definitions in the `Langlands.NYLL` namespace, under the
source's `variable` blocks and `Tower` section so that every target keeps the
source theorem's complete parameter telescope and universes. The `Tower` binders
of the M167.016 target are written in the definition itself, in source order,
so that the source hypothesis `[Finite E]` its statement does not use is kept.
The targets of the source `@[simp]` theorems are reducible (`abbrev`) so that
their later proofs can carry the attribute. Source proofs are omitted. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- Target of M167.004: an integer residue exponent maps to the corresponding
power of Frobenius. -/
abbrev finiteResidueFrobeniusExponentHom_intCastStatement (m : ℤ) : Prop :=
  finiteResidueFrobeniusExponentHom k L
      (Multiplicative.ofAdd (m : ZMod (Module.finrank k L))) =
    (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m

/-- Target of M167.005: residue exponent one maps to the arithmetic Frobenius
automorphism. -/
abbrev finiteResidueFrobeniusExponentHom_oneStatement : Prop :=
  finiteResidueFrobeniusExponentHom k L
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k L

/-- Target of M167.006: every finite residue-field automorphism is a power of
arithmetic Frobenius, so the canonical exponent homomorphism is onto. -/
def finiteResidueFrobeniusExponentHom_surjectiveStatement : Prop :=
  Function.Surjective (finiteResidueFrobeniusExponentHom k L)

/-- Target of M167.007: the finite-level Frobenius exponent homomorphism is
injective. -/
def finiteResidueFrobeniusExponentHom_injectiveStatement : Prop :=
  Function.Injective (finiteResidueFrobeniusExponentHom k L)

/-- Target of M167.012: the profinite Frobenius map depends on reduction modulo
the residue extension degree. -/
abbrev finiteResidueFrobeniusFromZHat_applyStatement (z : ZHatMul) : Prop :=
  finiteResidueFrobeniusFromZHat k L z =
    finiteResidueFrobeniusExponentHom k L
      (Multiplicative.ofAdd
        (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd))

/-- Target of M167.013: the distinguished profinite integer `1` acts as
arithmetic Frobenius. -/
abbrev finiteResidueFrobeniusFromZHat_oneStatement : Prop :=
  finiteResidueFrobeniusFromZHat k L
      (Multiplicative.ofAdd (1 : ZHat)) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k L

section Tower

/-- Target of M167.016: arithmetic Frobenius commutes with restriction in a
tower of finite extensions of a finite field.

The binders of the source's `Tower` section `variable` block are written here
in their source order, because a definition, unlike the source theorem, would
drop the section hypothesis `[Finite E]` that the statement does not use. -/
def restrictNormalHom_finiteResidueFrobeniusStatement
    {E : Type v} {F : Type w}
    [Field E] [Finite E] [Field F] [Finite F]
    [Algebra k E] [Algebra k F] [Algebra E F]
    [IsScalarTower k E F] [Normal k E] : Prop :=
  AlgEquiv.restrictNormalHom E
      (FiniteField.frobeniusAlgEquivOfAlgebraic k F) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k E

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

/-- Target of M167.017: the finite Frobenius exponent coordinates commute with
restriction.  The exponent on the smaller field is obtained by the canonical
reduction `Z/[F:k]Z → Z/[E:k]Z`. -/
def restrictNormalHom_finiteResidueFrobeniusExponentHomStatement
    (z : Multiplicative (ZMod (Module.finrank k F))) : Prop :=
  AlgEquiv.restrictNormalHom E
      (finiteResidueFrobeniusExponentHom k F z) =
    finiteResidueFrobeniusExponentHom k E
      (Multiplicative.ofAdd
        (ZMod.castHom
          (show Module.finrank k E ∣ Module.finrank k F from
            ⟨Module.finrank E F,
              (Module.finrank_mul_finrank k E F).symm⟩)
          (ZMod (Module.finrank k E)) z.toAdd))

/-- Target of M167.018: the actions of `ℤ̂` on finite residue extensions
commute with restriction in finite towers. -/
def restrictNormalHom_finiteResidueFrobeniusFromZHatStatement (z : ZHatMul) : Prop :=
  AlgEquiv.restrictNormalHom E
      (finiteResidueFrobeniusFromZHat k F z) =
    finiteResidueFrobeniusFromZHat k E z

end Tower

end
end Langlands.NYLL.LocalClassFieldTheory
