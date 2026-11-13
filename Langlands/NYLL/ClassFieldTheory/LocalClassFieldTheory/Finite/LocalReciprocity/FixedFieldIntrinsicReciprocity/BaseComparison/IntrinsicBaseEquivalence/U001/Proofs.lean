/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFiniteStatement
of M273.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U001 Statements module. Replace the
source proof (transport along closedFixingSubgroup_bot_eq_baseField from the
fixing subgroup of the bottom field) by a direct Mathlib proof: the fixing
subgroup of a finite-dimensional intermediate field is open, hence of finite
index in the compact Krull group. Omit all other declarations.
Worker 226, 13 November 2026: adopt the shared proof by Worker 57 for
submission with its original attribution and source correspondence.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U001.Statements

/-!
# Finite absolute quotient of an embedded finite extension

The proof of the published closed proposition that the fixing subgroup of the
image of a finite extension embedded in the separable closure has only
finitely many cosets in the whole absolute Galois group.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The fixing subgroup of the image of a finite extension embedded in
`SeparableClosure K` has finite index in the ambient base-field subgroup. -/
theorem ambientEmbeddedAbsoluteQuotientFinite :
    ambientEmbeddedAbsoluteQuotientFiniteStatement := by
  intro K F _ _ _ _ i
  dsimp only
  have : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  have hopen := (AlgHom.fieldRange i).fixingSubgroup_isOpen
  let := QuotientGroup.discreteTopology hopen
  have : Finite (Gal(SeparableClosure K / K) ⧸ (AlgHom.fieldRange i).fixingSubgroup) :=
    finite_of_compact_of_discrete
  have : (AlgHom.fieldRange i).fixingSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change Finite (_ ⧸ (AlgHom.fieldRange i).fixingSubgroup.subgroupOf _)
  exact Subgroup.finite_quotient_of_finiteIndex

end Langlands.NYLL.LocalClassFieldTheory
