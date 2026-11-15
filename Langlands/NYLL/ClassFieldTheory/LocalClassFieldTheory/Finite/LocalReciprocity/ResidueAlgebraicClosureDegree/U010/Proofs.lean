/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Frobenius.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U012.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U021.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U022.Proofs

/-!
# Finite local reciprocity: injectivity of Frobenius on a residue algebraic closure (proof)

Modified by Worker 46 and Worker 5163: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_injectiveStatement`
(M236.010) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks. The instances of the source's private
M236.002 (`IsAlgClosure k Omega`) and M236.003 (`IsGalois k Omega`) are
supplied by local `have`s, as in the target. The source proof is kept: Lean
unfolds the `Statement` types of the published theorems it applies and
rewrites with. The degree of the embedded subextension (the source's M236.009
theorem `finrank_finiteResidueGaloisIntermediateFieldIn`) is proved inside the
proof by the source's two-step `calc` (lines 104-110), with a local
`Fact (ringChar k).Prime` for the private M236.001, instead of importing a
separate proof of M236.009. See the paired Markdown and
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

/-- Finite subextensions of every positive degree detect every coordinate of
the canonical Frobenius homomorphism on an arbitrary residue algebraic
closure (M236.010). -/
theorem residueAbsoluteFrobenius_isAlgClosure_injective :
    residueAbsoluteFrobenius_isAlgClosure_injectiveStatement k Omega := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  show Function.Injective (residueAbsoluteFrobenius k Omega)
  intro z w hzw
  apply Multiplicative.ext
  apply ZHat.ext
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := finiteResidueGaloisIntermediateFieldIn k Omega n
  have hrestriction := congrArg (AlgEquiv.restrictNormalHom E) hzw
  rw [restrictNormalHom_residueAbsoluteFrobenius (z := z) (E := E),
    restrictNormalHom_residueAbsoluteFrobenius (z := w) (E := E)] at hrestriction
  let : Finite E := Module.finite_of_finite k
  change finiteResidueFrobeniusFromZHat k E z =
    finiteResidueFrobeniusFromZHat k E w at hrestriction
  rw [finiteResidueFrobeniusFromZHat_apply,
    finiteResidueFrobeniusFromZHat_apply] at hrestriction
  have hcoordinate := congrArg Multiplicative.toAdd
    (finiteResidueFrobeniusExponentHom_injective k E hrestriction)
  have hdegree : Module.finrank k E = n := by
    have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
    calc
      Module.finrank k E =
          Module.finrank k
            (FiniteField.Extension k (ringChar k) n) :=
        (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm
      _ = n := FiniteField.finrank_extension k (ringChar k) n
  simp only [toAdd_ofAdd] at hcoordinate
  change zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd =
    zHatReduction (Module.finrank k E) Module.finrank_pos w.toAdd at hcoordinate
  have hdiv : n ∣ Module.finrank k E := by simp [hdegree]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod n)) hcoordinate
  rw [zHatReduction_transition hn Module.finrank_pos hdiv z.toAdd,
    zHatReduction_transition hn Module.finrank_pos hdiv w.toAdd] at hcast
  exact hcast

end
end Langlands.NYLL.LocalClassFieldTheory
