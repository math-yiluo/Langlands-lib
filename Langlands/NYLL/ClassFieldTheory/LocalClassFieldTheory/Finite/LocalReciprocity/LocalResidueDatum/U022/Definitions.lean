/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 15 November 2026:
Extract M249.022 (localResidueDegree, lines 400–416) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespaces. In the source, the two
uses of residueAbsoluteDegreeIn find three instance arguments by instance
search. Fintype is the published instance localDecompositionResidueFintype
(M249.015). The two Prop-valued ones come from source instances whose
proofs are not published, so the body supplies them by local haveI facts
before the structure:
* Normal κ λ, from which instance search derives Algebra.IsAlgebraic κ λ,
  is the source instance decompositionResidueExtension_normal (M243.030,
  lines 394–413 of
  Nyll/ValuedFieldTheory/Ramification/HilbertRamification/
  ResidueExactSequence.lean), proved by its source proof for the
  valuation ring localSeparableValuationSubring K. Its private helpers
  decompositionGroup_action_locallyConstant, decompositionGroup_continuousSMul
  and decompositionGroup_compactSpace (M243.008–M243.010, lines 102–144) are
  inlined by their source proofs. Instance search finds the other two
  helpers M243.011–M243.012 (lines 146–163) through Mathlib's instance on
  FixedPoints.subring and the published instance
  decompositionFixedSubring.instIsInvariant.
* IsAlgClosed λ is the source instance localSelectedResidueIsAlgClosed
  (M249.016, lines 267–303), proved by its source proof. The private
  source valuation ring localAbsoluteValuationSubring (M249.003) is the
  published Langlands.NYLL.PortInternal.M249.d003, and the source theorem
  valuationSubring_residueField_isAlgClosed (M237.001) is the published
  Langlands.LocalGalois.residue_isAlgClosed, which has the same statement.
The source writes the structure with `where`; here it is a structure
instance after the haveI facts. Import the Library modules that publish the
declarations used instead of the source imports. Omit the open lines this
definition does not need and all other declarations. The docstring, type and
both structure fields are the source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U015.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.U006.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.DecompositionGroupIsClosedProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.ProfiniteInvariant.NormalProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.IsInvariantProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields
import Langlands.Galois.Local.SpectralProof

/-!
# The local residue degree map

For a nonarchimedean local field `K`, the continuous homomorphism
`Gal(SeparableClosure K / K) →ₜ* ZHatMul` obtained by composing the
continuous residue action on the selected residue field with the intrinsic
arithmetic-Frobenius degree of the algebraically closed residue extension.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open Langlands.NYLL.ClassFormation
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring
open scoped Pointwise

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

attribute [local instance] Langlands.NYLL.PortInternal.M249.d001

/-- **Finite local reciprocity, local degree map.**  The residue Frobenius degree,
defined directly on the separable-closure model used by the local reciprocity
formalization. -/
noncomputable def localResidueDegree :
    Gal(SeparableClosure K / K) →ₜ* ZHatMul :=
  -- M243.030 (source instance `decompositionResidueExtension_normal`), inlined
  haveI hNormal : Normal
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K)) := by
    let A := localSeparableValuationSubring K
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    -- M243.010 (source private `decompositionGroup_compactSpace`), inlined
    let : CompactSpace (decompositionGroup K A) := by
      have hc : IsCompact (decompositionGroup K A :
          Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) :=
        (Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosed
          K A).isCompact
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
    exact Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profinite
      (G := decompositionGroup K A)
      (decompositionFixedMaximalIdeal K A)
      (IsLocalRing.maximalIdeal A)
  -- M249.016 (source instance `localSelectedResidueIsAlgClosed`), inlined
  haveI : IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K)) := by
    let A := Langlands.NYLL.PortInternal.M249.d003 K
    let B := localSeparableValuationSubring K
    let barI := valuationSubringComapResidueMap
      (F := SeparableClosure K) A
    let : Algebra (selectedResidueField B) (selectedResidueField A) :=
      barI.toAlgebra
    let : IsPurelyInseparable (SeparableClosure K) (AlgebraicClosure K) :=
      separableClosure.isPurelyInseparable K (AlgebraicClosure K)
    let : IsPurelyInseparable (selectedResidueField B)
        (selectedResidueField A) :=
      valuationSubring_comap_residueField_isPurelyInseparable
        (F := SeparableClosure K) A
    let : PerfectField (decompositionResidueField K B) := inferInstance
    let : Algebra.IsAlgebraic (decompositionResidueField K B)
        (selectedResidueField B) :=
      hNormal.toIsAlgebraic
    let : PerfectField (selectedResidueField B) :=
      Algebra.IsAlgebraic.perfectField
        (K := decompositionResidueField K B)
        (L := selectedResidueField B)
    let : Algebra.IsSeparable (selectedResidueField B)
        (selectedResidueField A) := inferInstance
    have hsurjective : Function.Surjective barI :=
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable
        (selectedResidueField B) (selectedResidueField A)
    let e : selectedResidueField B ≃+* selectedResidueField A :=
      RingEquiv.ofBijective barI ⟨barI.injective, hsurjective⟩
    let : IsAlgClosed (selectedResidueField A) :=
      Langlands.LocalGalois.residue_isAlgClosed A
    exact IsAlgClosed.of_ringEquiv (selectedResidueField A)
      (selectedResidueField B) e.symm
  { toMonoidHom :=
      (residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))).toMonoidHom.comp
          (localSeparableResidueAlgAction K).toMonoidHom
    continuous_toFun :=
      (residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField
          (localSeparableValuationSubring K))).continuous_toFun.comp
        (localSeparableResidueAlgAction K).continuous_toFun }

end

end Langlands.NYLL.LocalClassFieldTheory
