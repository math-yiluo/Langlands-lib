import Langlands.TraceFormula.NormOneFinitePlaceGeometricTerm
import Langlands.TraceFormula.SingleOrbitSimpleTrace

/-! # Nonvanishing of an isolated trace from two orbital factors -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global AdelicGroupPoints PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.BaseChange
open AdelicGroupAutomorphism

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (v : FinitePlace K)
  (T : CommGroupScheme (Spec (CommRingCat.of K)))
  (i : T.toGrp ⟶ G) (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

local notation "H" => normOneSubgroup K G
local notation "M" => PlaceGroupPoints K G (Sum.inr v)

set_option maxRecDepth 3800 in
/-- A trace computed on one rational orbit is nonzero if the local and exterior
orbital factors are nonzero and a nonzero global orbital value implies finite
rational centralizer covolume. -/
def NormOneFinitePlaceTraceNonzeroStatement : Prop :=
  let μH : Measure H := Measure.haar
  let R := rationalNormOneSubgroup K G
  let D := normOneFinitePlaceDecomposition K G v T i hi I e hc
  let J := (normOneFinitePlaceProjection K G v).toMonoidHom.ker
  let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
  ∀ [MeasurableSpace M] [BorelSpace M] [μH.IsMulRightInvariant]
    (a : Aut G) (_ha : i ≫ a.asIso.hom = i) (r : R),
    let θ := (normOneAut K a).toMonoidHom
    let θv := G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v))
    let θJ := (normOneFinitePlaceKernelTwist K G v a).toMonoidHom
    let Cv := twistedCentralizer θv (D.symm (r : H)).1
    let Cj := twistedCentralizer θJ (D.symm (r : H)).2
    (∀ x y : twistedCentralizer θ (r : H), x * y = y * x) →
    ∀ (μv : Measure M) [μv.IsHaarMeasure]
      (μCv : Measure Cv) [μCv.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μCv]
      [μCv.IsOpenPosMeasure] (νv : Measure (LeftQuotient Cv)),
      IsCompatible Cv μv μCv νv →
    ∀ (fw : AdelicGroupPoints K G → ℂ),
      (∀ z x, fw (z * finitePlacePointInclusion K G v x) = fw z) →
    ∀ (fv : M → ℂ),
      twistedOrbitalIntegral θv (D.symm (r : H)).1 νv fv ≠ 0 →
      (∀ (νj : Measure (LeftQuotient Cj)), νj ≠ 0 → νj.Regular →
        (∀ j : J, MeasurePreserving (rightTranslate Cj j) νj νj) →
        twistedOrbitalIntegral θJ (D.symm (r : H)).2 νj
          (fun z : J => normOnePositiveAverage K G T i ρ fw z.val) ≠ 0) →
      let F := normOnePositiveAverage K G T i ρ (fun x => fv (atPlace K G (.inr v) x) * fw x)
      ∀ trace : ℂ,
      (∀ d : TwistedGeometricMeasures R θ (r : H) μH,
        (d.orbitalValue F ≠ 0 → d.rational Set.univ ≠ ⊤) ∧ trace = d.term F) →
      trace ≠ 0

set_option maxRecDepth 4200 in
set_option maxHeartbeats 2000000 in
theorem normOneFinitePlaceTraceNonzero :
    NormOneFinitePlaceTraceNonzeroStatement K G v T i hi I e hc := by
  unfold NormOneFinitePlaceTraceNonzeroStatement
  intro μH R D J ρ _ _ _ a ha r θ θv θJ Cv Cj hComm μv _ μCv _ _ _ νv hνv
    fw hfw fv hLocal hExt F trace hTrace
  obtain ⟨νj, d, hνj, hReg, hInv, hFactor⟩ :=
    normOneFinitePlaceGeometricTerm K G v T i hi I e hc a ha r hComm μv μCv νv hνv
  have hValue : d.orbitalValue F ≠ 0 := by
    change twistedOrbitalIntegral θ (r : H) d.orbital F ≠ 0
    rw [(hFactor fw hfw fv).1]
    exact mul_ne_zero hLocal (hExt νj hνj hReg hInv)
  obtain ⟨hFinite, hTerm⟩ := hTrace d
  rw [hTerm]
  change ((d.rational Set.univ).toReal : ℂ) * d.orbitalValue F ≠ 0
  exact mul_ne_zero (d.covolume_ne_zero (hFinite hValue)) hValue

end Langlands.TraceFormula
