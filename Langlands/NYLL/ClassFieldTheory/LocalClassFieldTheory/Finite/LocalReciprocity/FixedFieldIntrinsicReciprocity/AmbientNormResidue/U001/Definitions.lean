/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M282.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and preserve the source telescope, docstring and abbreviation body.
Replace the source imports by the Mathlib modules that supply the separable
closure, Galois extensions, nonarchimedean local fields and valuation
extensions. Omit the unused namespace openings and all other declarations of
the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension

/-!
# The ambient separable-closure equivalence type

The type of `F`-algebra equivalences from the separable closure of `F` to
the separable closure of `K`, where the target is made an `F`-algebra
through a `K`-embedding of the Galois extension `E` of `F`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

/-- The separable-closure equivalence used to compare the intrinsic extension
over `F` with its realization inside the ambient separable closure of `K`. -/
abbrev ambientEmbeddedSeparableClosureEquiv
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :=
  @AlgEquiv F (SeparableClosure F) (SeparableClosure K)
    _ _ _
    (separableClosure F (AlgebraicClosure F)).algebra
    (j.comp (IsScalarTower.toAlgHom K F E)).toRingHom.toAlgebra

end

end Langlands.NYLL.LocalClassFieldTheory
