/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: prove only M265.012 (source lines 154–200 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) as
Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embedding,
whose type is the published localSeparableValuationSubring_comap_embeddingStatement.
The source proof identifies both valuation rings with the chosen integral-closure
target through the unported uniqueness theorem
target_valuationSubring_eq_of_finite_separable (M196.039); this proof instead
shows that the integral-closure valuation ring of the published M245.017 witness
lies in both rings and uses that a discrete valuation ring has no proper
overrings other than the whole field. The pullback property of the chosen
separable valuation ring (source M249.007, lines 94–104 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean,
with its private lemma M249.004, lines 66–76) is reproved inline as a `have`,
following the source proof. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison.ComapEmbeddingStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFProof

/-!
# Pulling the chosen separable valuation ring back along an embedding: proof

Proof of NYLL M265.012.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002

/-- Pulling the selected extension valuation on `Kˢᵉᵖ` back along a finite
separable embedding gives the given local valuation on the source field. -/
theorem localSeparableValuationSubring_comap_embedding :
    localSeparableValuationSubring_comap_embeddingStatement := by
  intro K L _ _ _ _ _ _ _ _ _ i _
  let base := Langlands.NYLL.LocalFieldTheory.localCompleteDVF K
  obtain ⟨target, hmem, -⟩ :=
    Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF
      K L base
  -- The integral-closure valuation ring is contained in every valuation ring
  -- of `L` lying over the base valuation ring, and equals each of them.
  have key : ∀ D : ValuationSubring L,
      (∀ x : K, algebraMap K L x ∈ D ↔ x ∈ base.valuation.valuationSubring) →
        target.valuation.valuationSubring = D := by
    intro D hD
    have hle : target.valuation.valuationSubring ≤ D := by
      intro z hz
      have hint : IsIntegral base.valuation.valuationSubring z := (hmem z).1 hz
      let φ : base.valuation.valuationSubring →+* D :=
        { toFun := fun a => ⟨algebraMap K L a, (hD a).2 a.2⟩
          map_one' := by ext; simp
          map_mul' := by intro a b; ext; simp
          map_zero' := by ext; simp
          map_add' := by intro a b; ext; simp }
      have hcomp : (algebraMap D L).comp φ =
          algebraMap base.valuation.valuationSubring L := by
        ext a
        rfl
      have hintD : IsIntegral D z := by
        apply RingHom.IsIntegralElem.of_comp (f := φ)
        rw [hcomp]
        exact hint
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintD
      rw [← hy]
      exact y.2
    have hne : D ≠ ⊤ := by
      intro htop
      have hbase : base.valuation.valuationSubring = ⊤ := by
        ext x
        simp only [ValuationSubring.mem_top, iff_true]
        exact (hD x).1 (htop ▸ ValuationSubring.mem_top _)
      exact (Valuation.valuationSubring_eq_top_iff base.valuation).mp hbase inferInstance
    exact ValuationSubring.eq_of_le_of_ne_top _ hle hne
  -- The pullback of the chosen separable valuation ring to `K` (source M249.007,
  -- with its private lemma M249.004 inlined as in the source).
  have hpull : ∀ x : K, algebraMap K (SeparableClosure K) x ∈ localSeparableValuationSubring K ↔
      x ∈ base.valuation.valuationSubring := by
    intro x
    have habsolute : ∀ y : K,
        algebraMap K (AlgebraicClosure K) y ∈
            Langlands.NYLL.PortInternal.M249.d003 K ↔
          y ∈ base.valuation.valuationSubring := by
      intro y
      rcases Classical.choose_spec
          (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
            (L := AlgebraicClosure K) base.valuation) with
        ⟨_hmap, _hlocal, hpullback⟩
      exact hpullback y
    change algebraMap (SeparableClosure K) (AlgebraicClosure K)
        (algebraMap K (SeparableClosure K) x) ∈
          Langlands.NYLL.PortInternal.M249.d003 K ↔ _
    rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
      (AlgebraicClosure K)]
    exact habsolute x
  have hB : ∀ x : K, algebraMap K L x ∈ (localSeparableValuationSubring K).comap i.toRingHom ↔
      x ∈ base.valuation.valuationSubring := by
    intro x
    change i (algebraMap K L x) ∈ localSeparableValuationSubring K ↔ _
    rw [i.commutes]
    exact hpull x
  have hC : ∀ x : K, algebraMap K L x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      x ∈ base.valuation.valuationSubring := by
    intro x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔ base.valuation x ≤ 1
    rw [Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    rfl
  exact (key _ hB).symm.trans (key _ hC)

end Langlands.NYLL.LocalClassFieldTheory
