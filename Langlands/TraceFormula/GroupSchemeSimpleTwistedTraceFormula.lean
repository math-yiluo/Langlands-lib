import Langlands.TraceFormula.PositiveQuotientTwistedTraceComparisonProof
import Langlands.TraceFormula.PositiveQuotientTraceComparisonProof
import Langlands.TraceFormula.AbstractSimpleTwistedProof
import Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction
import Langlands.TraceFormula.QuotientRightRegular
import Langlands.TraceFormula.TwistedSupportCompact
import Langlands.Analysis.TraceClassIdealProof

/-!
# The simple twisted trace formula on `L²([G])` from closed elliptic twisted orbits

Let `G` be an affine group scheme of finite type over a number field `F`, with a central split
torus `T → G` as in the Library's `L²([G])`, and let `τ` be an automorphism of `G` of finite
order fixing `T`. Write `Θ` and `θ` for its actions on `G(𝔸_F)` and `G(𝔸_F)¹`, `Γ = G(F)`, and
`fOne(x) = ∫_{A⁺} f(a x) da` for `f ∈ C_c(G(𝔸_F))`.

`groupSchemeSimpleTwistedTraceFormula` states: if `R(f)` is trace class on `L²([G])` and
finitely many pairwise non-twisted-conjugate points `r j ∈ Γ` with closed twisted orbits in
`G(𝔸_F)¹` and compact quotients `(Γ ∩ C_{r j}) \ C_{r j}` represent every rational class on
whose twisted orbit `fOne` does not vanish identically, then for all compatible measures the
centralizer volumes are finite, the twisted orbit functions of `fOne` are integrable and

`tr (R(f) ∘ I_Θ) = ∑ j, vol((Γ ∩ C_{r j}) \ C_{r j}) · TO_{r j}(fOne)`.

The proof passes to `L²(Γ \ G(𝔸_F)¹)` with `PositiveQuotientTwistedTraceComparisonStatement`
(proved by `positiveQuotientTwistedTraceComparison`) and applies
`AbstractSimpleTwistedTraceFormulaStatement` (proved by `abstractSimpleTwistedTraceFormula`) to
`G(𝔸_F)¹`, `Γ`, `θ` and the right regular representation `quotientRightRegular`. Its support
hypothesis is `exists_isCompact_twistedSupport`; the volumes and integrability come from
`twistedCentralizerAnalyticConditions_of_compact_closed`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

set_option maxHeartbeats 1000000 in
/-- The simple twisted trace formula on `L²([G])` for a finite-order automorphism fixing the
central split torus, under closedness of the twisted orbits and compactness of the centralizer
quotients of finitely many rational representatives covering the support of `fOne`. -/
theorem groupSchemeSimpleTwistedTraceFormula (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (τ : Aut G) (hτ : IsOfFinOrder τ) (hfix : i ≫ τ.asIso.hom = i) :
    ∃ (hΘ : ∀ x, adelicAut F τ x ∈ positiveRationalSubgroup F G T i ↔
        x ∈ positiveRationalSubgroup F G T i)
      (hΘμ : MeasurePreserving
        (quotientAutomorphism (positiveRationalSubgroup F G T i) (adelicAut F τ) hΘ).symm
        (positiveRationalQuotientHaarMeasure F G T i)
        (positiveRationalQuotientHaarMeasure F G T i)),
    ∀ (f : AdelicGroupPoints F G → ℂ), Continuous f → HasCompactSupport f →
      ∀ (h : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G))),
      IsTraceClass (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h) →
    let fOne : normOneSubgroup F G → ℂ := fun x =>
      ∫ a, f (positivePointMap F G T i a * x) ∂normalizedPositiveHaarMeasure F G T i hi I e hc
    ∀ (m : ℕ) (r : Fin m → rationalNormOneSubgroup F G),
      (∀ j, IsClosed (TwistedOrbit (normOneAut F τ) (r j : normOneSubgroup F G))) →
      (∀ j, CompactSpace (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
        (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G))))) →
      (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup F G) (normOneAut F τ)
        (r j : normOneSubgroup F G) (r k : normOneSubgroup F G) → j = k) →
      (∀ q ∈ rationalNormOneSubgroup F G,
        (∃ x : normOneSubgroup F G, fOne (x⁻¹ * q * normOneAut F τ x) ≠ 0) →
        ∃ j, IsTwistedConjugate (rationalNormOneSubgroup F G) (normOneAut F τ)
          (r j : normOneSubgroup F G) q) →
      ∀ [∀ j, MeasurableSpace (LeftQuotient (twistedCentralizer (normOneAut F τ)
            (r j : normOneSubgroup F G)))]
        [∀ j, BorelSpace (LeftQuotient (twistedCentralizer (normOneAut F τ)
            (r j : normOneSubgroup F G)))]
        [∀ j, MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
            (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G))))]
        [∀ j, BorelSpace (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
            (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G))))]
        (μC : ∀ j, Measure (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G)))
        [∀ j, (μC j).IsMulRightInvariant] [∀ j, IsFiniteMeasureOnCompacts (μC j)]
        [∀ j, (μC j).IsOpenPosMeasure]
        (νC : ∀ j, Measure (LeftQuotient (twistedCentralizer (normOneAut F τ)
            (r j : normOneSubgroup F G))))
        (νΓC : ∀ j, Measure (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
            (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G))))),
        (∀ j, IsCompatible (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G))
          (Measure.haar : Measure (normOneSubgroup F G)) (μC j) (νC j)) →
        (∀ j, IsCompatible ((rationalNormOneSubgroup F G).subgroupOf
            (twistedCentralizer (normOneAut F τ) (r j : normOneSubgroup F G)))
          (μC j) Measure.count (νΓC j)) →
        (∀ j, νΓC j Set.univ ≠ ⊤) ∧
        (∀ j, Integrable (twistedOrbitFunction (normOneAut F τ) (r j : normOneSubgroup F G)
          fOne) (νC j)) ∧
        operatorTrace ((haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h).comp
            (twistOperator (positiveRationalSubgroup F G T i) (adelicAut F τ) hΘ
              (positiveRationalQuotientHaarMeasure F G T i) hΘμ)) =
          ∑ j, ((νΓC j Set.univ).toReal : ℂ) *
            twistedOrbitalIntegral (normOneAut F τ) (r j : normOneSubgroup F G) (νC j) fOne := by
  obtain ⟨hΘ, hΘμ, hcomp⟩ := positiveQuotientTwistedTraceComparison F G T i hi I e hc τ hτ hfix
  refine ⟨hΘ, hΘμ, ?_⟩
  intro f hf hfc h htr fOne m r hclosed hcompact hpair hcover _ _ _ _ μC _ _ _ νC νΓC hμC hνΓC
  let fC : C_c(AdelicGroupPoints F G, ℂ) := ⟨⟨f, hf⟩, hfc⟩
  let Γ := rationalNormOneSubgroup F G
  let θ := normOneAut F τ
  let ν := normOneRationalQuotientHaarMeasure F G
  have hνc : IsCompatible Γ (Measure.haar : Measure (normOneSubgroup F G)) Measure.count ν :=
    normOneRationalQuotientHaarMeasure_isCompatible F G
  let : SigmaCompactSpace (normOneSubgroup F G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hΓclosed : IsClosed (Γ : Set (normOneSubgroup F G)) :=
    Γ.isClosed_of_isDiscrete (isDiscrete_rationalNormOneSubgroup F G)
  -- `fOne` is continuous with compact support
  obtain ⟨hcont, hcs, -⟩ := positiveQuotientTraceComparison F G T i hi I e hc fC
  let fOneC : C_c(normOneSubgroup F G, ℂ) := ⟨⟨fOne, hcont⟩, hcs⟩
  have hOne : Integrable fOne (Measure.haar : Measure (normOneSubgroup F G)) :=
    hcont.integrable_of_hasCompactSupport hcs
  -- the right regular representation on `L²(Γ \ G(𝔸_F)¹)`
  let : T2Space (LeftQuotient Γ) := leftQuotient_t2Space Γ hΓclosed
  let : ν.Regular := hνc.regular
  let : LocallyCompactSpace (LeftQuotient Γ) := leftQuotient_locallyCompactSpace Γ
  let π := quotientRightRegular Γ ν hνc.right_invariant
  have hπnorm := norm_quotientRightRegular_apply Γ ν hνc.right_invariant
  have hπmeas := aestronglyMeasurable_quotientRightRegular_apply Γ ν hνc.right_invariant
    (Measure.haar : Measure (normOneSubgroup F G))
  have hπ := quotientRightRegular_coeFn Γ ν hνc.right_invariant
  obtain ⟨hTiff, hTeq⟩ := hcomp fC h hOne π hπnorm hπmeas hπ
  have htrΘ := isTraceClass_precomp _
    (twistOperator (positiveRationalSubgroup F G T i) (adelicAut F τ) hΘ
      (positiveRationalQuotientHaarMeasure F G T i) hΘμ) htr
  -- volumes, integrability and the support hypothesis
  have hanalytic := fun j => twistedCentralizerAnalyticConditions_of_compact_closed Γ θ
    (r j : normOneSubgroup F G) (hcompact j) (hclosed j)
  have hvol : ∀ j, νΓC j Set.univ ≠ ⊤ := fun j => (hanalytic j).1 (μC j) (νΓC j) (hνΓC j)
  have hint : ∀ j, Integrable (twistedOrbitFunction θ (r j : normOneSubgroup F G) fOne)
      (νC j) := fun j => (hanalytic j).2 (μC j) (νC j) (hμC j) fOne hcont hcs
  have hsupp := exists_isCompact_twistedSupport Γ θ (fun j => (r j : normOneSubgroup F G))
    hcompact hclosed fOne hcs.isCompact hcover
  refine ⟨hvol, hint, ?_⟩
  refine (hTeq htrΘ).trans ?_
  exact abstractSimpleTwistedTraceFormula (Measure.haar : Measure (normOneSubgroup F G)) Γ ν hνc θ
    (normOneAut_mem_rationalNormOneSubgroup_iff F τ)
    (measurePreserving_normOneAut F τ hτ)
    (measurePreserving_rationalQuotientAut_symm F τ hτ) π hπnorm hπmeas hπ fOneC
    (hTiff.mp htrΘ) hsupp m r hpair hcover μC νC νΓC hμC hνΓC hvol hint

end Langlands.TraceFormula
