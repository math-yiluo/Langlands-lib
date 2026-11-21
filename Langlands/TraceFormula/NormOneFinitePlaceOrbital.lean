import Langlands.TraceFormula.FinitePlacePositiveTensor
import Langlands.TraceFormula.TwistedOrbitalProduct
import Langlands.Analysis.Local.ProductHaarNormalization
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.Global.LocalModularCharacterAdjointDeterminantStatement

/-! # Finite-place orbital integration with the actual norm-one Haar measure -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration AdelicGroupAutomorphism

universe u

section Exterior

variable {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y]

private theorem exteriorQuotient_exists (C : Subgroup Y) (hC : IsClosed (C : Set Y))
    (μY : Measure Y) [μY.IsHaarMeasure] [μY.IsMulRightInvariant]
    (hcomm : ∀ x y : C, x * y = y * x)
    [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)] :
    ∃ (μC : Measure C) (_ : μC.IsHaarMeasure) (hR : μC.IsMulRightInvariant),
      letI := hR
      ∃ ν : Measure (LeftQuotient C), IsCompatible C μY μC ν := by
  let : LocallyCompactSpace C := hC.locallyCompactSpace
  let : SecondCountableTopology C := TopologicalSpace.Subtype.secondCountableTopology (C : Set Y)
  let : BorelSpace C := Subtype.borelSpace (· ∈ C)
  let μC : Measure C := Measure.haar
  have hR : μC.IsMulRightInvariant := ⟨fun y => by
    have h : (fun x : C => x * y) = fun x => y * x := funext fun x => hcomm x y
    rw [h, map_mul_left_eq_self]⟩
  exact ⟨μC, inferInstance, hR, compatibleMeasureExists C hC μY μC⟩

end Exterior

section NormOne

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (v : Langlands.Global.FinitePlace K)
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

local notation "H" => normOneSubgroup K G
local notation "M" => PlaceGroupPoints K G (Sum.inr v)

set_option maxRecDepth 3000 in
/-- The chosen local quotient measure extends to a compatible norm-one
orbital quotient measure with exact finite-place tensor factorization. -/
def NormOneFinitePlaceOrbitalStatement : Prop :=
  let μH : Measure H := Measure.haar
  let P := normOneFinitePlaceProjection K G v
  let J := P.toMonoidHom.ker
  let D := normOneFinitePlaceDecomposition K G v T i hi I e hc
  let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
  ∀ [MeasurableSpace M] [BorelSpace M] [μH.IsMulRightInvariant]
    (a : Aut G) (_ha : i ≫ a.hom = i) (δ : H),
    let θ := (normOneAut K a).toMonoidHom
    let θv := G.affinePointsTarget a.hom (placeCompletion K (.inr v))
    let θJ := (normOneFinitePlaceKernelTwist K G v a).toMonoidHom
    let Cv := twistedCentralizer θv (D.symm δ).1
    let Cj := twistedCentralizer θJ (D.symm δ).2
    let C := twistedCentralizer θ δ
    (∀ x y : C, x * y = y * x) →
    ∀ [MeasurableSpace (LeftQuotient Cv)] [BorelSpace (LeftQuotient Cv)]
      [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)]
      (μv : Measure M) [μv.IsHaarMeasure]
      (μCv : Measure Cv) [μCv.IsMulRightInvariant]
      [IsFiniteMeasureOnCompacts μCv] [μCv.IsOpenPosMeasure]
      (νv : Measure (LeftQuotient Cv)),
      IsCompatible Cv μv μCv νv →
      let _ : MeasurableSpace (LeftQuotient Cj) := borel _
      ∃ (νj : Measure (LeftQuotient Cj)) (μC : Measure C) (ν : Measure (LeftQuotient C)),
        νj ≠ 0 ∧ νj.Regular ∧ (∀ j : J, MeasurePreserving (rightTranslate Cj j) νj νj) ∧
        IsFiniteMeasureOnCompacts μC ∧ μC.IsOpenPosMeasure ∧
        ∃ hR : μC.IsMulRightInvariant,
          letI := hR
          IsCompatible C μH μC ν ∧
          ∀ (fv : M → ℂ) (fw : AdelicGroupPoints K G → ℂ),
            (∀ z x, fw (z * finitePlacePointInclusion K G v x) = fw z) →
            twistedOrbitalIntegral θ δ ν
                (normOnePositiveAverage K G T i ρ
                  (fun x => fv (atPlace K G (.inr v) x) * fw x)) =
              twistedOrbitalIntegral θv (D.symm δ).1 νv fv *
                twistedOrbitalIntegral θJ (D.symm δ).2 νj
                  (fun z : J => normOnePositiveAverage K G T i ρ fw z.val)

set_option maxRecDepth 3400 in
set_option maxHeartbeats 3800000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem normOneFinitePlaceOrbital : NormOneFinitePlaceOrbitalStatement K G v T i hi I e hc := by
  unfold NormOneFinitePlaceOrbitalStatement
  intro μH P J D ρ _ _ hμH a ha δ θ θv θJ Cv Cj C hcomm
    mV bV mC bC μv _ μCv _ _ _ νv hCvCompat
  let : LocallyCompactSpace (Langlands.Global.FiniteCompletion K v) :=
    (isCompact_adicCompletionIntegers K v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers K).zero_mem)
  let : LocallyCompactSpace M :=
    G.affinePointsLocallyCompactSpace (placeCompletion K (.inr v))
  let : SecondCountableTopology J := TopologicalSpace.Subtype.secondCountableTopology (J : Set H)
  let : BorelSpace J := Subtype.borelSpace (· ∈ J)
  have hJ : IsClosed (J : Set H) := isClosed_eq P.continuous continuous_const
  let : LocallyCompactSpace J := hJ.locallyCompactSpace
  have hθ (p : M × J) : θ (D p) = D (θv p.1, θJ p.2) :=
    normOneFinitePlaceDecomposition_twist K G v T i hi I e hc a ha p
  have hCv : IsClosed (Cv : Set M) :=
    isClosed_twistedCentralizer θv
      (G.continuous_affinePointsTarget (placeCompletion K (.inr v)) a.hom) (D.symm δ).1
  have hCj : IsClosed (Cj : Set J) :=
    isClosed_twistedCentralizer θJ
      (normOneFinitePlaceKernelTwist K G v a).continuous (D.symm δ).2
  let : LocallyCompactSpace Cv := hCv.locallyCompactSpace
  let : LocallyCompactSpace Cj := hCj.locallyCompactSpace
  let : SecondCountableTopology Cv := TopologicalSpace.Subtype.secondCountableTopology (Cv : Set M)
  let : SecondCountableTopology Cj := TopologicalSpace.Subtype.secondCountableTopology (Cj : Set J)
  let : SigmaFinite μCv := SigmaFinite.of_isFiniteMeasureOnCompacts μCv
  let E := (prodSubgroupHomeomorph Cv Cj).symm.trans
    (twistedCentralizerProductEquiv D θv θJ θ hθ δ)
  let j : Cj →* C := E.toMonoidHom.comp (MonoidHom.inr Cv Cj)
  have hj : Function.Injective j := fun x y h => congrArg Prod.snd (E.injective h)
  have hcommJ (x y : Cj) : x * y = y * x := by
    apply hj
    rw [map_mul, map_mul, hcomm]
  obtain ⟨μJ, hJHaar, _, hJRight, hprod⟩ :=
    productHaarNormalization D μv μH inferInstance inferInstance hμH
  let := hJHaar
  let := hJRight
  let : MeasurableSpace (LeftQuotient Cj) := borel _
  let : BorelSpace (LeftQuotient Cj) := ⟨rfl⟩
  obtain ⟨μCj, hCjHaar, hCjRight, νj, hCjCompat⟩ :=
    exteriorQuotient_exists Cj hCj μJ hcommJ
  let := hCjHaar
  let := hCjRight
  let : SigmaFinite μCj := SigmaFinite.of_isFiniteMeasureOnCompacts μCj
  let : MeasurableSpace (LeftQuotient (twistedCentralizer θv (D.symm δ).1)) := mV
  let : BorelSpace (LeftQuotient (twistedCentralizer θv (D.symm δ).1)) := bV
  let : MeasurableSpace (LeftQuotient (twistedCentralizer θ δ)) := mC
  let : BorelSpace (LeftQuotient (twistedCentralizer θ δ)) := bC
  let μC := twistedCentralizerProductMeasure D θv θJ θ hθ δ μCv μCj
  let ν := twistedOrbitProductMeasure D θv θJ θ hθ δ νv νj
  obtain ⟨hCompat, hFactor⟩ :=
    twistedOrbitalProduct D θv θJ θ hθ δ μv μJ μCv μCj νv νj hCv hCj hCvCompat hCjCompat
  refine ⟨νj, μC, ν, hCjCompat.nonzero, hCjCompat.regular, hCjCompat.right_invariant,
    inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← hprod]
    exact hCompat
  · intro fv fw hfw
    let F := normOnePositiveAverage K G T i ρ (fun x => fv (atPlace K G (.inr v) x) * fw x)
    let W : J → ℂ := fun y => normOnePositiveAverage K G T i ρ fw y.val
    have hF : F = fun z => fv (D.symm z).1 * W (D.symm z).2 := by
      funext z
      have hz := finitePlacePositiveTensor K G v T i hi I e hc fv fw hfw (D.symm z)
      change F (D (D.symm z)) = fv (D.symm z).1 * W (D.symm z).2 at hz
      rwa [D.apply_symm_apply] at hz
    change twistedOrbitalIntegral θ δ ν F =
      twistedOrbitalIntegral θv (D.symm δ).1 νv fv * twistedOrbitalIntegral θJ (D.symm δ).2 νj W
    rw [hF]
    exact hFactor fv W

end NormOne

end Langlands.TraceFormula
