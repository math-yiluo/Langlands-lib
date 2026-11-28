import Langlands.Analysis.HilbertSumTraceProof
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalDecompositionProof
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-!
# A cuspidal summand carrying a nonzero trace

If the integrated action `R(f)` on `L²` of the positive rational quotient is trace class, has
range in the cuspidal subspace `S` and has nonzero trace, and if `S` is the Hilbert sum of a
family of irreducible closed invariant subspaces, then one member `P` of the family has a trace
class compression of `R_S(f)` with nonzero trace. See `CuspidalSummandTraceExtraction.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

/-- The compression to the cuspidal subspace of an integrated action with cuspidal range is the
cuspidal integrated action. -/
theorem cuspidalCompression_eq_of_range (ν : Measure (AdelicGroupPoints F G))
    (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)
    (hS : ∀ φ, haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ ∈
      fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).orthogonalProjectionOnto ∘L
        haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf ∘L
        (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).subtypeL =
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf := by
  apply ContinuousLinearMap.ext
  intro φ
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  have h : (⟨haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ.val, hS φ.val⟩ : S) =
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf φ :=
    Subtype.ext (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν f hf φ).symm
  change S.orthogonalProjectionOnto (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf
    φ.val) = _
  rw [← h]
  exact S.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hS φ.val⟩

set_option maxHeartbeats 1600000 in
/-- **A summand with nonzero compressed trace.** Let `R(f)` be trace class on `L²` of the
positive rational quotient, with range in the cuspidal subspace `S` and nonzero trace. Suppose
the cuspidal integrated actions of compactly supported continuous weights are compact, so that
`S` is the Hilbert sum of irreducible closed invariant subspaces. Then some irreducible closed
invariant subspace `P` of `S` has a trace class compression of `R_S(f)` with nonzero trace. -/
theorem exists_irreducibleSummand_compressedTrace_ne_zero
    (hcpt : ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f Measure.haar),
      IsCompactOperator (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc
        Measure.haar f hf))
    (ν : Measure (AdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)
    (hTC : IsTraceClass (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf))
    (hS : ∀ φ, haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ ∈
      fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc)
    (hne : operatorTrace (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf) ≠ 0) :
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∃ P : Submodule ℂ S, (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
          (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      ∃ hP : CompleteSpace P, haveI := hP
        let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
          fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf ∘L P.subtypeL
        IsTraceClass (E := (P : Submodule ℂ S)) RPf ∧
          operatorTrace (E := (P : Submodule ℂ S)) RPf ≠ 0 := by
  intro S πc
  obtain ⟨h₁, h₂⟩ := hilbertSumTrace.{u, u}
  have hR := cuspidalCompression_eq_of_range F G hPD hG T i hi I e hc ν f hf hS
  obtain ⟨hRtc, hRtr⟩ := h₁ _ S _ hTC hS
  rw [hR] at hRtc hRtr
  obtain ⟨A, hA, hsum, -⟩ := groupSchemeFullAEL2CuspidalDecomposition F G hPD hG T i hi I e hc hcpt
  let : ∀ P : A, CompleteSpace P.val := fun P => (hA P.val P.property).2.1.completeSpace_coe
  obtain ⟨htc, -, hhas, -⟩ := h₂ S A (fun P => P.val) hsum _ hRtc
  by_contra hall
  have hzero : ∀ P : A, operatorTrace (E := (P.val : Submodule ℂ S))
      (P.val.orthogonalProjectionOnto ∘L
        fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf ∘L P.val.subtypeL :
          P.val →L[ℂ] P.val) = 0 := by
    intro P
    by_contra hP
    exact hall ⟨P.val, hA P.val P.property, inferInstance, htc P, hP⟩
  have h0 : HasSum (fun P : A => operatorTrace (E := (P.val : Submodule ℂ S))
      (P.val.orthogonalProjectionOnto ∘L
        fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf ∘L P.val.subtypeL :
          P.val →L[ℂ] P.val)) 0 := by
    simp only [hzero]
    exact hasSum_zero
  exact hne (hRtr.symm.trans (hhas.unique h0))

end Langlands.TraceFormula
