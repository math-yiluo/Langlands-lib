import Langlands.TraceFormula.NormOneFinitePlaceOrbital
import Langlands.TraceFormula.ExtendTwistedGeometricMeasures
import Langlands.Global.AdelicGroupRationalTopology

/-! # Finite-place factor of an exact geometric trace term -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.BaseChange AdelicGroupAutomorphism

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (v : Langlands.Global.FinitePlace K)
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

local notation "H" => normOneSubgroup K G
local notation "M" => PlaceGroupPoints K G (Sum.inr v)

set_option maxRecDepth 3300 in
/-- The weighted orbital term factors at the chosen finite place with one
fixed package of compatible orbital and rational centralizer measures. -/
def NormOneFinitePlaceGeometricTermStatement : Prop :=
  let μH : Measure H := Measure.haar
  let R := rationalNormOneSubgroup K G
  let P := normOneFinitePlaceProjection K G v
  let J := P.toMonoidHom.ker
  let D := normOneFinitePlaceDecomposition K G v T i hi I e hc
  let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
  ∀ [MeasurableSpace M] [BorelSpace M] [μH.IsMulRightInvariant]
    (a : Aut G) (_ha : i ≫ a.asIso.hom = i) (r : R),
    let θ := (normOneAut K a).toMonoidHom
    let θv := G.affinePointsTarget a.asIso.hom (placeCompletion K (.inr v))
    let θJ := (normOneFinitePlaceKernelTwist K G v a).toMonoidHom
    let Cv := twistedCentralizer θv (D.symm (r : H)).1
    let Cj := twistedCentralizer θJ (D.symm (r : H)).2
    let C := twistedCentralizer θ (r : H)
    (∀ x y : C, x * y = y * x) →
    ∀ [MeasurableSpace (LeftQuotient Cv)] [BorelSpace (LeftQuotient Cv)]
      (μv : Measure M) [μv.IsHaarMeasure]
      (μCv : Measure Cv) [μCv.IsMulRightInvariant]
      [IsFiniteMeasureOnCompacts μCv] [μCv.IsOpenPosMeasure]
      (νv : Measure (LeftQuotient Cv)),
      IsCompatible Cv μv μCv νv →
      let fOne (fv : M → ℂ) (fw : AdelicGroupPoints K G → ℂ) :=
        normOnePositiveAverage K G T i ρ (fun x => fv (atPlace K G (.inr v) x) * fw x)
      ∃ (νj : Measure (LeftQuotient Cj)) (d : TwistedGeometricMeasures R θ (r : H) μH),
        νj ≠ 0 ∧ νj.Regular ∧ (∀ j : J, MeasurePreserving (rightTranslate Cj j) νj νj) ∧
        ∀ (fw : AdelicGroupPoints K G → ℂ),
          (∀ z x, fw (z * finitePlacePointInclusion K G v x) = fw z) →
          let Oext := twistedOrbitalIntegral θJ (D.symm (r : H)).2 νj
            (fun z : J => normOnePositiveAverage K G T i ρ fw z.val)
          ∀ fv : M → ℂ,
            let Oloc := twistedOrbitalIntegral θv (D.symm (r : H)).1 νv fv
            twistedOrbitalIntegral θ (r : H) d.orbital (fOne fv fw) = Oloc * Oext ∧
              d.term (fOne fv fw) = (((d.rational Set.univ).toReal : ℂ) * Oext) * Oloc

set_option maxRecDepth 4200 in
set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem normOneFinitePlaceGeometricTerm : NormOneFinitePlaceGeometricTermStatement K G v T i hi I e hc := by
  unfold NormOneFinitePlaceGeometricTermStatement
  intro μH R P J D ρ _ _ _ a ha r θ θv θJ Cv Cj C hcomm _ _ μv _ μCv _ _ _ νv hνv fOne
  obtain ⟨νj, μC, ν, hJ, hReg, hInv, hFin, hPos, hRight, hν, hFactor⟩ :=
    normOneFinitePlaceOrbital K G v T i hi I e hc a ha (r : H) hcomm μv μCv νv hνv
  let := hFin
  let := hPos
  let := hRight
  obtain ⟨d, _, hOrb⟩ := extendTwistedGeometricMeasures R θ (r : H) μH
    (normOneAut K a).continuous (isDiscrete_rationalNormOneSubgroup K G) hcomm μC ν hν
  refine ⟨νj, d, hJ, hReg, hInv, ?_⟩
  intro fw hfw Oext fv Oloc
  have hEqual : twistedOrbitalIntegral θ (r : H) d.orbital (fOne fv fw) = Oloc * Oext := by
    rw [hOrb]
    exact hFactor fv fw hfw
  refine ⟨hEqual, ?_⟩
  change ((d.rational Set.univ).toReal : ℂ) *
    twistedOrbitalIntegral θ (r : H) d.orbital (fOne fv fw) = _
  rw [hEqual]
  ac_rfl

end Langlands.TraceFormula
