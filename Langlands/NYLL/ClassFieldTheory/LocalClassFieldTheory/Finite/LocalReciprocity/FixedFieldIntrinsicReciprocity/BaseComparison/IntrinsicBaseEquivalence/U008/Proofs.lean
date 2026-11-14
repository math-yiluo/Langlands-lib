/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement
of M273.008 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U007 Statements module, which contains
the statement. Replace the source proof (a calc chain through M273.007) by a
direct pointwise computation that does not use M273.007: the value is
e0 (e0.symm (e (tau (e.symm (e0 (e0.symm x)))))) by definition, which
simplifies to e (tau (e.symm x)). Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U007.Statements

/-!
# Intrinsic-to-ambient embedded base equivalence: action on the closure

The proof of the published closed proposition that
`intrinsicBaseEquivAmbientEmbeddedField K F i e tau` acts on
`SeparableClosure K` by `x ↦ e (tau (e.symm x))`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology
open ClassFormation

/-- The embedded-field base equivalence acts on the ambient separable closure
by conjugating the intrinsic automorphism through the chosen equivalence. -/
theorem intrinsicBaseEquivAmbientEmbeddedField_apply_val :
    intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement := by
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e tau x
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    ((AlgEquiv.ofInjectiveField i).trans
      (IntermediateField.equivOfEq
        (InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)).symm)).toLinearEquiv.finiteDimensional
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  show e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x)))))) =
    e (tau.1 (e.symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end Langlands.NYLL.LocalClassFieldTheory
