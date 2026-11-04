import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets
import Langlands.Representation.Aubert.General.CorrectedGradedReduction
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalPointSecondCountable

/-! # The rational surviving graded transitions from explicit structural inputs

`RationalCorrectedGradedTransitionInputs` collects, for the actual standard
families on `RationalPoint k G.X`, the structural facts used by the conditional
reduction `correctedGradedTransitionTarget_of_orbitData` and the orbit Jacquet
data `nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups` that the Library
does not already prove. The theorem
`rationalCorrectedGradedTransitionStatement_of_inputs` proves the exact
`RationalCorrectedGradedTransitionStatement` from these inputs; σ-compactness,
closedness of the standard parabolics and continuity of the Levi projections come
from published Library theorems. No inhabitant of the inputs is constructed.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The structural inputs for the surviving graded transitions on the actual
standard families, under the premises of
`RationalCorrectedGradedTransitionStatement`: every standard parabolic has
compact quotient, and at every grade `n` with length-ordered Weyl element `w`,
every lift `m` of `w⁻¹` and every surviving `J = S \ s` the following hold:

* the support sets `G_{θ_n'}` and `G_{θ_{n+1}'}` satisfy
  `SurvivingSupportHypotheses` (both open, the larger one left
  `P_J`-invariant, their difference the single cell `P_J m⁻¹ P_I`);
* for every `K` with `L_K = m⁻¹ L_I m`: `m⁻¹ U_I m ∩ P_J ⊆ U_K`,
  `m (L_J ∩ U_K) m⁻¹ ⊆ U_I`, and the modulus identity
  `δ_{U_I}(l) δ_{U_K}(m⁻¹ l m) = δ_{U_I ∩ m U_K m⁻¹}(l)²` on `L_I`. -/
def RationalCorrectedGradedTransitionInputs : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (_hOrder : StandardParabolicOrderStatement.{u})
      (_hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (_hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
      letI : DecidableEq (Weyl i) := Classical.decEq _
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        let h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν
        (∀ J, CompactSpace (Induction.LeftQuotient (parabolic i ν J))) ∧
        (∀ (I s : Finset (SimpleRoot i ν)) (n : ℕ)
          (hn : n < (Support.rankOrderedList cs.length).length)
          (m : Group.RelativeWeyl.normalizer (torusPoints i)),
          (QuotientGroup.mk m : Weyl i) = (Support.rankOrderedElement cs.length n hn)⁻¹ →
          IsMinimal cs (Finset.univ \ s) I (Support.rankOrderedElement cs.length n hn) →
          CorrectedFiltration.SurvivingSupportHypotheses (parabolic i ν) (torusPoints i) cs
            I s n (m : RationalPoint k G.X)) ∧
        (∀ (I : Finset (SimpleRoot i ν)) (n : ℕ)
          (hn : n < (Support.rankOrderedList cs.length).length)
          (m : Group.RelativeWeyl.normalizer (torusPoints i)),
          (QuotientGroup.mk m : Weyl i) = (Support.rankOrderedElement cs.length n hn)⁻¹ →
          ∀ (K : Finset (SimpleRoot i ν))
            (hK : ∀ x : RationalPoint k G.X,
              x ∈ levi i ν I ↔ (m : RationalPoint k G.X)⁻¹ * x * m ∈ levi i ν K),
            (∀ s, K ⊆ Finset.univ \ s →
              IsMinimal cs (Finset.univ \ s) I (Support.rankOrderedElement cs.length n hn) →
              ∀ x ∈ unipotent i ν I, (m : RationalPoint k G.X)⁻¹ * x * m ∈
                  parabolic i ν (Finset.univ \ s) →
                (m : RationalPoint k G.X)⁻¹ * x * m ∈ unipotent i ν K) ∧
            (∀ s, K ⊆ Finset.univ \ s →
              IsMinimal cs (Finset.univ \ s) I (Support.rankOrderedElement cs.length n hn) →
              ∀ x ∈ levi i ν (Finset.univ \ s), x ∈ unipotent i ν K →
                (m : RationalPoint k G.X) * x * (m : RationalPoint k G.X)⁻¹ ∈
                  unipotent i ν I) ∧
            ∀ l : levi i ν I,
              (HaarModulus.closedRestrictCharacter (unipotent i ν I) (hU I) (levi i ν I)
                  (h I).levi_le_normalizer l : ℝ≥0) *
                  (HaarModulus.closedRestrictCharacter (unipotent i ν K) (hU K) (levi i ν K)
                    (h K).levi_le_normalizer (conjugationEquiv (m : RationalPoint k G.X) hK l) :
                    ℝ≥0) =
                (HaarModulus.closedRestrictCharacter
                    (CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I)
                      (unipotent i ν K) (m : RationalPoint k G.X))
                    (CorrectedFiltration.isClosed_orbitUnipotentIntersection (hU I) (hU K)
                      (m : RationalPoint k G.X)) (levi i ν I)
                    (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection
                      (h I) (h K) (m : RationalPoint k G.X) hK) l : ℝ≥0) ^ 2)

/-- The structural inputs prove the exact `RationalCorrectedGradedTransitionStatement`:
`G(k)` is σ-compact by `reductiveRationalPoint_secondCountable`, the standard
parabolics are closed by `isClosed_standard_parabolic`, the Levi projections are
continuous by `continuous_standard_projection`, the orbit Jacquet data at every
grade come from `nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups`, with
`U_I ∩ P_I` a limit of compact subgroups by `isLimitOfCompactSubgroups_subgroupOf`,
and `correctedGradedTransitionTarget_of_orbitData` assembles the graded maps. -/
theorem rationalCorrectedGradedTransitionStatement_of_inputs
    (H : RationalCorrectedGradedTransitionInputs.{u}) :
    RationalCorrectedGradedTransitionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _
  let : DecidableEq (Weyl i) := Classical.decEq _
  intro CM cs hlen hpos hlevi
  obtain ⟨hcpt, hsupp, hS⟩ :=
    H k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM cs hlen hpos hlevi
  have : SecondCountableTopology (RationalPoint k G.X) :=
    reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (RationalPoint k G.X) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have := hcpt
  have hPc : ∀ J, IsClosed (parabolic i ν J : Set (RationalPoint k G.X)) := fun J =>
    isClosed_standard_parabolic i ν hStandard hG hi hν J
  have hr : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
        I).projection := fun I =>
    continuous_standard_projection i ν hStandard hG hi hν I
  have hNc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν I).subgroupOf (parabolic i ν I)) := fun I =>
    isLimitOfCompactSubgroups_subgroupOf (unipotent i ν I) (parabolic i ν I) (hPc I) (hUc I)
  exact CorrectedFiltration.correctedGradedTransitionTarget_of_orbitData.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν) (rootAssociation i ν hN hZ)
    (torusPoints i) cs hPc hsupp hNc
    (fun I E _ n hn m hm K hK =>
      (CorrectedFiltration.nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardUnipotent_antitone i ν hOrder hG hi hν)
        (standardParabolic_monotone i ν hOrder hG hi hν) hPc (torusPoints i) cs I E
        (Support.rankOrderedElement cs.length n hn) (m : RationalPoint k G.X) K hK
        (hS I n hn m hm K hK).1 (hS I n hn m hm K hK).2.1 (hr I) (hS I n hn m hm K hK).2.2
        (hNc I)).some)

end Langlands.Aubert.General.RationalPointFamily
