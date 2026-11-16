/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 15 November 2026:
Extract M249.024 (localResidueDatum, lines 436–441) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespaces. The field degree is the
source term. The source field degree_surjective is the theorem
localResidueDegree_surjective K (M249.023), whose proof is not published;
here the field is a tactic proof of the same proposition:
* the surjectivity of the residue action localSeparableResidueAlgAction K
  (M249.021, lines 393–398) is proved by the source proofs of M249.021,
  residueAlgActionOfEqTop_surjective (M244.004, lines 72–85 of
  Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
  ResidueActionIndex.lean) and decompositionGroupResidueAction_surjective
  (M243.029, lines 356–392 of
  Nyll/ValuedFieldTheory/Ramification/HilbertRamification/
  ResidueExactSequence.lean), with the private helpers of M243.029
  (M243.008–M243.010, lines 102–144) inlined by their source proofs and
  M243.011–M243.012 (lines 146–163) supplied by instance search;
* the surjectivity of localResidueDegree K is then the source proof of
  M249.023 (lines 420–434), stated for arbitrary proofs of the two
  Prop-valued instance arguments that localResidueDegree K supplies to
  residueAbsoluteDegreeIn, and applied to the proofs in that definition.
The source writes the structure with `where`, as here. Import the Library
modules that publish the declarations used instead of the source imports.
Omit the open lines this definition does not need and all other
declarations. The docstring, type and the field degree are the source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U022.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum.Initial.Definitions
import Mathlib.RingTheory.Invariant.Profinite

/-!
# The local residue degree datum

For a nonarchimedean local field `K`, the abstract class-formation degree
datum `Gal(SeparableClosure K / K) → ZHatMul` given by the local residue
degree map, together with its surjectivity.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open Langlands.NYLL.ClassFormation
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
open scoped Pointwise

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Finite local reciprocity.**  The actual abstract class-formation datum
`d : G_K -> ZHat` furnished by the residue action of a local field. -/
noncomputable def localResidueDatum :
    DegreeData (Gal(SeparableClosure K / K)) where
  degree := localResidueDegree K
  degree_surjective := by
    let A := localSeparableValuationSubring K
    -- M243.029 (source theorem `decompositionGroupResidueAction_surjective`),
    -- inlined for `A`
    have h029 : Function.Surjective (decompositionGroupResidueAction K A) := by
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := ⟨rfl⟩
      -- M243.010 (source private `decompositionGroup_compactSpace`), inlined
      let : CompactSpace (decompositionGroup K A) := by
        have hc : IsCompact (decompositionGroup K A :
            Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) :=
          (decompositionGroup_isClosed K A).isCompact
        exact isCompact_iff_compactSpace.mp hc
      -- M243.009 (source private `decompositionGroup_continuousSMul`), inlined
      let : ContinuousSMul (decompositionGroup K A) A := by
        constructor
        rw [continuous_prod_of_discrete_right]
        intro a
        -- M243.008 (source private `decompositionGroup_action_locallyConstant`),
        -- inlined
        have hlc : IsLocallyConstant
            (fun g : decompositionGroup K A ↦ g • a) := by
          rw [IsLocallyConstant.iff_exists_open]
          intro sigma
          let E : IntermediateField K (SeparableClosure K) :=
            IntermediateField.adjoin K {(a : SeparableClosure K)}
          let : FiniteDimensional K E :=
            IntermediateField.adjoin.finiteDimensional
              (Algebra.IsIntegral.isIntegral (a : SeparableClosure K))
          let U : Set (decompositionGroup K A) :=
            ((↑) : decompositionGroup K A →
                (SeparableClosure K ≃ₐ[K] SeparableClosure K)) ⁻¹'
              (((sigma : SeparableClosure K ≃ₐ[K] SeparableClosure K)) •
                (E.fixingSubgroup :
                  Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)))
          refine ⟨U, E.fixingSubgroup_isOpen.smul
              (sigma : SeparableClosure K ≃ₐ[K] SeparableClosure K)
                |>.preimage continuous_subtype_val, ?_, ?_⟩
          · exact ⟨1, E.fixingSubgroup.one_mem, mul_one _⟩
          · intro tau htau
            rcases htau with ⟨g, hg, heq⟩
            have hga : g (a : SeparableClosure K) = (a : SeparableClosure K) :=
              (IntermediateField.mem_fixingSubgroup_iff E g).mp hg
                (a : SeparableClosure K)
                (IntermediateField.subset_adjoin (F := K)
                  (S := {(a : SeparableClosure K)})
                  (Set.mem_singleton (a : SeparableClosure K)))
            apply Subtype.ext
            change (((tau : decompositionGroup K A) :
                  SeparableClosure K ≃ₐ[K] SeparableClosure K)
                  (a : SeparableClosure K)) =
              (((sigma : decompositionGroup K A) :
                  SeparableClosure K ≃ₐ[K] SeparableClosure K)
                  (a : SeparableClosure K))
            rw [← heq]
            simp [AlgEquiv.mul_apply, hga]
        exact hlc.continuous
      intro sigma
      obtain ⟨tau, htau⟩ :=
        Ideal.Quotient.stabilizerHom_surjective_of_profinite
          (G := decompositionGroup K A)
          (decompositionFixedMaximalIdeal K A)
          (IsLocalRing.maximalIdeal A) sigma
      refine ⟨tau.1, ?_⟩
      have htau_eq :
          decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1 = tau := by
        apply Subtype.ext
        rfl
      change
        Ideal.Quotient.stabilizerHom
            (IsLocalRing.maximalIdeal A)
            (decompositionFixedMaximalIdeal K A)
            (decompositionGroup K A)
            (decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1) =
          sigma
      rw [htau_eq]
      exact htau
    -- M244.004 (source theorem `residueAlgActionOfEqTop_surjective`) and
    -- M249.021 (source theorem `localSeparableResidueAlgAction_surjective`),
    -- inlined for `A` and `hA := localSeparableDecompositionGroup_eq_top K`
    have h021 : Function.Surjective (localSeparableResidueAlgAction K) := by
      have hA : decompositionGroup K A = ⊤ :=
        localSeparableDecompositionGroup_eq_top K
      change Function.Surjective (residueAlgActionOfEqTop K A hA)
      intro tau
      obtain ⟨sigma, hsigma⟩ := h029 tau
      refine ⟨(sigma : SeparableClosure K ≃ₐ[K] SeparableClosure K), ?_⟩
      have heq :
          toDecompositionGroupOfEqTop K A hA
            (sigma : SeparableClosure K ≃ₐ[K] SeparableClosure K) = sigma := by
        ext
        rfl
      simpa [residueAlgActionOfEqTop, heq] using hsigma
    -- M249.023 (source theorem `localResidueDegree_surjective`), for any
    -- proofs of the two Prop-valued instance arguments of
    -- `residueAbsoluteDegreeIn` that are not global instances
    have h023 : ∀ (_ : Algebra.IsAlgebraic
          (decompositionResidueField K (localSeparableValuationSubring K))
          (selectedResidueField (localSeparableValuationSubring K)))
        (_ : IsAlgClosed
          (selectedResidueField (localSeparableValuationSubring K))),
        Function.Surjective
          ((residueAbsoluteDegreeIn
            (decompositionResidueField K (localSeparableValuationSubring K))
            (selectedResidueField (localSeparableValuationSubring K))).comp
              (localSeparableResidueAlgAction K)) := by
      intro _ _ z
      obtain ⟨tau, htau⟩ :=
        (residueDatumIn
          (decompositionResidueField K (localSeparableValuationSubring K))
          (selectedResidueField
            (localSeparableValuationSubring K))).degree_surjective z
      obtain ⟨sigma, hsigma⟩ := h021 tau
      refine ⟨sigma, ?_⟩
      change residueAbsoluteDegreeIn
          (decompositionResidueField K (localSeparableValuationSubring K))
          (selectedResidueField (localSeparableValuationSubring K))
            (localSeparableResidueAlgAction K sigma) = z
      rw [hsigma]
      simpa [residueDatumIn] using htau
    exact h023 _ _

end

end Langlands.NYLL.LocalClassFieldTheory
