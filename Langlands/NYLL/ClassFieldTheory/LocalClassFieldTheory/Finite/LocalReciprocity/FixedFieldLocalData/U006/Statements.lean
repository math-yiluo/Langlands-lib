/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statements of M272.006 and M272.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldLocalData.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix,
also in the opened namespace, and the suffix Statement. Import the two
Library modules that publish localSeparableValuationSubring and
decompositionGroup instead of the source imports. Omit the noncomputable
section, the open lines these statements do not need, and all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions

/-!
# The chosen valuation rings under a finite separable extension: statements

Two closed propositions about a finite separable extension `F / K` of
nonarchimedean local fields, an embedding `i : F →ₐ[K] SeparableClosure K`,
and an `F`-algebra equivalence `e : SeparableClosure F ≃ₐ[F] SeparableClosure K`
(with `SeparableClosure K` an `F`-algebra through `i`): `e` identifies the
chosen valuation rings `localSeparableValuationSubring F` and
`localSeparableValuationSubring K`, and the decomposition group over `F` of
`localSeparableValuationSubring K` is the whole group.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- A separable-closure equivalence extending an embedding of a finite
separable local extension identifies the two uniquely extended local
valuation rings. -/
def localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement :
    Prop :=
  ∀ (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K),
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap e.toRingHom

/-- After identifying separable closures over a finite separable local
extension, the ambient selected valuation ring is stabilized by the whole
absolute Galois group of the extension field. -/
def localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement :
    Prop :=
  ∀ (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K),
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      decompositionGroup F (localSeparableValuationSubring K) = ⊤

end Langlands.NYLL.LocalClassFieldTheory
