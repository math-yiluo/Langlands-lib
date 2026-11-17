import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness

/-! # Haar invariance on the actual split-central quotient -/

noncomputable section

universe uG u

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Haar

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (A : Subgroup Γ) [A.Normal] (hA : A ≤ Subgroup.center Γ)

include hA in
omit [A.Normal] in
private theorem conjugation_preserves_centralSubgroup (g x : Γ) :
    conjugationContinuousMulEquiv g x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    have hcomm := Subgroup.mem_center_iff.mp (hA hx) g
    have hfix : conjugationContinuousMulEquiv g x = x := by
      change g * (g * x * g⁻¹) = (g * x * g⁻¹) * g at hcomm
      simpa [conjugationContinuousMulEquiv, mul_assoc] using
        congrArg (fun y => g⁻¹ * y) hcomm
    rwa [hfix] at hx
  · intro hx
    have hcomm := Subgroup.mem_center_iff.mp (hA hx) g
    change g * x * g⁻¹ ∈ A
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

/-- Ambient inner conjugation induces the actual inner automorphism of the
quotient by a central subgroup. -/
def centralSubgroupQuotientConjugation (g : Γ) : (Γ ⧸ A) ≃ₜ* (Γ ⧸ A) :=
  QuotientIntegration.quotientGroupAutomorphism A (conjugationContinuousMulEquiv g)
    (conjugation_preserves_centralSubgroup A hA g)

variable [T2Space Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (hAc : IsClosed (A : Set Γ))
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]

include hA hAc in
/-- Quotienting a unimodular group by a closed central subgroup preserves right
invariance of every regular Haar measure, including the original measure. -/
theorem centralSubgroupQuotient_isMulRightInvariant
    (hmod : ∀ g : Γ, modularCharacter g = 1)
    (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure] [mu.Regular] :
    mu.IsMulRightInvariant := by
  have : LocallyCompactSpace A := hAc.locallyCompactSpace
  let : MeasurableSpace A := borel _
  have : BorelSpace A := ⟨rfl⟩
  let muG : Measure Γ := haar
  let muA : Measure A := haar
  have : muA.IsMulRightInvariant := by
    constructor
    intro a
    have he : (fun x : A => x * a) = (fun x => a * x) := by
      funext x
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hA a.property) x)
    rw [he, map_mul_left_eq_self]
  have : muG.IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one hmod muG
  apply isMulRightInvariant_of_conjugationHaarChar_eq_one _ mu
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    let α := conjugationContinuousMulEquiv g
    let hα := conjugation_preserves_centralSubgroup A hA g
    have hαA : QuotientIntegration.subgroupAutomorphism A α hα =
        ContinuousMulEquiv.refl A := by
      ext a
      have hcomm := Subgroup.mem_center_iff.mp (hA a.property) g
      change g * (a : Γ) * g⁻¹ = a
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hαQ : QuotientIntegration.quotientGroupAutomorphism A α hα =
        conjugationContinuousMulEquiv (g : Γ ⧸ A) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x => rfl
    have he := QuotientIntegration.mulEquivHaarChar_eq_mul_quotientGroupAutomorphism
      A hAc muG muA α hα
    dsimp only at he
    rw [show mulEquivHaarChar α = 1 from
      mulEquivHaarChar_conjugation_eq_one muG g, hαA,
      mulEquivHaarChar_refl (G := A), one_mul, hαQ] at he
    exact he.symm

end Langlands.Haar

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Every Haar measure on the Borel quotient by the actual split-component
point image is right invariant and invariant under inversion. -/
theorem rationalSplitCentralQuotientHaar_invariant
    (hG : IsConnectedReductive G) (s : T.toGrp ⟶ G) (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure],
      mu.IsMulRightInvariant ∧ mu.IsInvInvariant := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  have : BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := ⟨rfl⟩
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : NonarchimedeanGroup (rationalPoints G) := Plancherel.rationalPoints_nonarchimedeanGroup G
  have hAc := isClosed_range_splitComponent G s hs
  have : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) := hAc
  intro mu _
  have : mu.Regular := inferInstance
  have hr : mu.IsMulRightInvariant := Haar.centralSubgroupQuotient_isMulRightInvariant
    (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center hAc
    (Aubert.General.RationalPointFamily.rationalReductiveUnimodularity F G hG
      standardCocharacter) mu
  let := hr
  exact ⟨hr, Langlands.isInvInvariant_of_isMulRightInvariant mu⟩

end Langlands.HarishChandraSchwartz
