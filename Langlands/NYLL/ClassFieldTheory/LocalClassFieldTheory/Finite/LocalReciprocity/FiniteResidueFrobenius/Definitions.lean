/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.Profinite
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# Finite local reciprocity: finite residue Frobenius coordinates (data)

Modified by Worker 123: extract the data commands M167.003 and M167.011 of the
pinned NYLL `FiniteResidueFrobenius` source and prefix the namespace with
`Langlands.NYLL`. The private M167.001 homomorphism and private M167.002 order
proof are inlined at their only use in M167.003, so neither becomes a separate
declaration. The source imports `Mathlib.SetTheory.Cardinal.Finite` (used only
by a source proof) and the NYLL degree module are replaced by the published
`ZHatMul`/`zHatReduction` data. Types, bodies, universes and the noncomputable
section are retained. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- The canonical finite-level exponent homomorphism
`Z/[L:k]Z → Gal(L/k)`, sending `1` to arithmetic Frobenius.

The integer-power homomorphism `ℤ →+ Additive (L ≃ₐ[k] L)` of the source's
private `finiteResidueFrobeniusIntegerPowers` and the source's private proof
`finiteResidueFrobeniusIntegerPowers_degree_eq_zero` that it kills the degree
are written in place. -/
def finiteResidueFrobeniusExponentHom :
    Multiplicative (ZMod (Module.finrank k L)) →* (L ≃ₐ[k] L) :=
  AddMonoidHom.toMultiplicative
    (ZMod.lift (Module.finrank k L)
      ⟨zmultiplesHom (Additive (L ≃ₐ[k] L)) (Additive.ofMul
          (FiniteField.frobeniusAlgEquivOfAlgebraic k L)),
        by
          apply Additive.ext
          change (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^
              (Module.finrank k L : ℤ) = 1
          rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := k) (L := L)]
          rw [zpow_natCast, pow_orderOf_eq_one]⟩)

/-- A profinite exponent acts on a finite residue extension through reduction
modulo its degree. -/
def finiteResidueFrobeniusFromZHat :
    ZHatMul →ₜ* (L ≃ₐ[k] L) where
  toFun z := finiteResidueFrobeniusExponentHom k L
    (Multiplicative.ofAdd
      (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd))
  map_one' := by
    apply (finiteResidueFrobeniusExponentHom k L).map_one
  map_mul' x y := by
    apply (finiteResidueFrobeniusExponentHom k L).map_mul
  continuous_toFun := by
    apply continuous_of_discreteTopology.comp
    exact continuous_ofAdd.comp
      ((zHatReduction (Module.finrank k L) Module.finrank_pos).continuous_toFun.comp
        continuous_toAdd)

end
end Langlands.NYLL.LocalClassFieldTheory
