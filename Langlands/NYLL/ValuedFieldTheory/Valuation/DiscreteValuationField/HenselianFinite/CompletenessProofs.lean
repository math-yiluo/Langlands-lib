/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 874 (2026-10-28): adapt the proofs of M105.001
(AdicPower.lean, lines 28-52) and M191.013/M191.014 (HenselianFinite.lean,
lines 224-275) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709
to prove the published closed targets `IsAdicCompleteOfLinearEquivStatement`
and `IsAdicCompleteOfModuleFiniteStatement`; prefix the namespace with
Langlands.NYLL; make M191.013 a private helper; shorten the M105.001 proof to
a composition of bijections; use focused Mathlib-only imports.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.Statements
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Small

/-!
# Proofs of adic completeness under linear equivalence and for finite modules

This module proves the two closed targets of
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.Statements`
(NYLL M105.001 and M191.014) with the ring and module universes independent.
The same-universe finite-module case (NYLL M191.013) is a private helper.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- Adic completeness is preserved by a linear equivalence of modules over the
same base ring and with respect to the same ideal (NYLL M105.001). -/
theorem isAdicComplete_of_linearEquiv.{u, v, w} :
    IsAdicCompleteOfLinearEquivStatement.{u, v, w} := by
  intro R M N _ _ _ _ _ I e _
  refine AdicCompletion.of_bijective_iff.mp ?_
  have h : (AdicCompletion.of I N : N → AdicCompletion I N) =
      AdicCompletion.congr I e ∘ AdicCompletion.of I M ∘ e.symm := by
    funext y
    simp [AdicCompletion.congr_apply, AdicCompletion.map_of]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

/-- Same-universe finite modules over a Noetherian adically complete ring are
adically complete (NYLL M191.013). -/
private theorem isAdicComplete_of_moduleFinite_sameUniverse.{u}
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    [IsNoetherianRing R] [Module.Finite R M] [IsAdicComplete I R] :
    IsAdicComplete I M := by
  refine AdicCompletion.of_bijective_iff.mp ?_
  let e : M ≃ₗ[R] AdicCompletion I M :=
    (TensorProduct.lid R M).symm ≪≫ₗ
      TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M) ≪≫ₗ
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have hone : AdicCompletion.of I R 1 = 1 :=
    (AdicCompletion.algebraMap_apply (S := R) I (1 : R)).symm.trans
      (map_one (algebraMap R (AdicCompletion I R)))
  have heq : (e : M → AdicCompletion I M) = AdicCompletion.of I M := by
    funext x
    simp [e, hone]
  rw [← heq]
  exact e.bijective

/-- A finite module over a Noetherian adically complete ring is adically
complete for the same ideal, with independent ring and module universes
(NYLL M191.014). -/
theorem isAdicComplete_of_moduleFinite.{u, v} :
    IsAdicCompleteOfModuleFiniteStatement.{u, v} := by
  intro R M _ _ _ I _ _ _
  have : Small.{u} M := Module.Finite.small R M
  have : Module.Finite R (Shrink.{u} M) :=
    Module.Finite.equiv (Shrink.linearEquiv R M).symm
  have : IsAdicComplete I (Shrink.{u} M) :=
    isAdicComplete_of_moduleFinite_sameUniverse I
  exact isAdicComplete_of_linearEquiv.{u, u, v} R (Shrink.{u} M) M I
    (Shrink.linearEquiv R M)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
