/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 450, 14 November 2026:
Extract the instance M299.006 (source lines 105-113) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix. Replace the three source imports by the published Library module of
intrinsicFiniteAbstractBase, which imports the modules of
intrinsicAbsoluteGalois, intrinsicAbstractBase, baseField, extensionSubgroup
and le_baseField. Open only CyclicCohomology and ClassFormation, the
namespaces of the published extensionSubgroup, baseField and le_baseField.
The section variable, docstring, modifiers, instance type and proof are
otherwise unchanged. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Definitions

/-!
# NYLL M299.006: the intrinsic absolute base has finite index in `baseField`

The finite quotient of the distinguished base fixing group of
`Gal(SeparableClosure K/K)` by the extension subgroup of the intrinsic
abstract base `intrinsicAbstractBase K`, registered as an instance from the
finiteness field of the published `intrinsicFiniteAbstractBase K`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

variable (K : Type) [Field K]

/-- The closed fixing group of the ground field is absolutely finite in the
abstract Galois-theoretic sense (indeed, it is the full absolute Galois group). -/
noncomputable instance intrinsicAbstractBase_index_finite :
    Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K))
        (intrinsicAbstractBase K) (le_baseField (intrinsicAbstractBase K))) := by
  exact (intrinsicFiniteAbstractBase K).finite

end Langlands.NYLL.LocalClassFieldTheory

end
