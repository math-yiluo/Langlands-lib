/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_applyStatement
of M273.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U007 Statements module. Replace the
source proof (comparison of autCongr e0 thetaTau with rho using the
M099.005 instance) by a pointwise computation: the left side acts on
SeparableClosure K by e0 (e0.symm (e (tau (e.symm (e0 (e0.symm x)))))),
which simplifies to the right side's e (tau (e.symm x)). Omit all other declarations.
Worker 695, 14 November 2026: retain this shared draft proof and update
the historical dependency description against the current Library.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U007.Statements

/-!
# Intrinsic-to-ambient embedded base equivalence: value as a subgroup element

The proof of the published closed proposition that
`intrinsicBaseEquivAmbientEmbeddedField K F i e tau` is the ambient
fixed-field subgroup element corresponding to the conjugate
`e ∘ tau ∘ e⁻¹`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology
open ClassFormation

/-- The intrinsic-to-ambient equivalence is the fixed-field subgroup element
obtained by conjugating the intrinsic automorphism through the chosen
separable-closure equivalence. -/
theorem intrinsicBaseEquivAmbientEmbeddedField_apply :
    intrinsicBaseEquivAmbientEmbeddedField_applyStatement := by
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e tau
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
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
