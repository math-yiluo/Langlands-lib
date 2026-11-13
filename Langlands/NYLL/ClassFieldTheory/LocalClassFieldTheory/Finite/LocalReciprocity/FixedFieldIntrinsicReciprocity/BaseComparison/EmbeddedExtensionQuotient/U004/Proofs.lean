/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finiteStatement
of M274.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U003 Statements module. Replace the
source proof (transport of finiteness from the intrinsic abstract base along
intrinsicBaseEquivAmbientEmbeddedField) by a direct Mathlib proof: the fixing
subgroup of the finite-dimensional image of E is open, hence of finite index
in the compact Krull group, hence of finite index in every subgroup containing
it. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Statements

/-!
# Finiteness of embedded extension quotients

The proof of the published closed proposition that the fixing subgroup of the
image of a finite Galois extension `E / F` has only finitely many cosets in the
fixing subgroup of the image of `F`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The relative quotient of fixing subgroups attached to an embedded
finite Galois extension is finite. -/
theorem ambientEmbeddedExtensionQuotient_finite :
    ambientEmbeddedExtensionQuotient_finiteStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j i _e H₀ J₀
  have : FiniteDimensional K E := Module.Finite.trans F E
  have : FiniteDimensional K (AlgHom.fieldRange j) :=
    (AlgEquiv.ofInjectiveField j).toLinearEquiv.finiteDimensional
  have hopen := (AlgHom.fieldRange j).fixingSubgroup_isOpen
  let := QuotientGroup.discreteTopology hopen
  have : Finite (Gal(SeparableClosure K / K) ⧸ (AlgHom.fieldRange j).fixingSubgroup) :=
    finite_of_compact_of_discrete
  have : (AlgHom.fieldRange j).fixingSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change Finite (_ ⧸ (AlgHom.fieldRange j).fixingSubgroup.subgroupOf _)
  exact Subgroup.finite_quotient_of_finiteIndex

end Langlands.NYLL.LocalClassFieldTheory
