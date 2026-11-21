import Langlands.Automorphic.GroupSchemeFullAEL2Continuous

/-! # Pointwise cuspidality of continuous representatives of full AE cusp classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "μG₁" => (Measure.haar : Measure (normOneSubgroup F G))
local notation "U" => properRationalParabolicRadicals hPD hG
local notation "μU" => properParabolicQuotientMeasure F G hPD hG

/-- The constant term of a continuous function along a proper parabolic radical is
continuous, by joint continuity of the integrand and compactness of the radical quotient. -/
theorem continuous_normalizedParabolicConstantTerm (P : ProperRationalParabolic G)
    (f : ContinuousRationalFunctions F G) :
    Continuous (constantTerm F G (U P) (μU P) f) := by
  have h : Continuous (Function.uncurry (constantTermIntegrand F G (U P) f)) := by
    let hq := LeftCosetSpace.isOpenQuotientMap_mk (AdelicSubgroupPoints.rationalSubgroup F G (U P))
    rw [← (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff]
    change Continuous (fun p : AdelicGroupPoints F G × AdelicSubgroupPoints.adelicPoints F G (U P) =>
      evaluate F G f ((p.2 : AdelicGroupPoints F G) * p.1))
    exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  exact continuousOn_univ.mp (continuousOn_integral_of_compact_support
    («μ» := μU P) (f := constantTermIntegrand F G (U P) f) (k := univ)
    isCompact_univ h.continuousOn (by simp))

variable (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

/-- A period of a positive-central quotient function at an arbitrary adelic point
is the corresponding period evaluated at its norm-one projection. -/
theorem positiveQuotientConstantTerm_normOneProjection (P : ProperRationalParabolic G)
    (f : C(Q, ℂ)) (a : AdelicGroupPoints F G) :
    constantTerm F G (U P) (μU P) (positiveQuotientContinuousPullback F G T i f) a =
      properParabolicPositivePeriod F G hPD hG T i P f
        (normOneProjection F G T i hi I e hc a) := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun q => ?_
  obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective
    (AdelicSubgroupPoints.rationalSubgroup F G (U P)) q
  rw [constantTermIntegrand_mk, properParabolicPositivePeriodIntegrand_mk]
  change f (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) (n.val * a)) = _
  apply congrArg f
  have h := positiveQuotientHomeomorph_rightTranslate F G T i hi I e hc a
    (LeftCosetSpace.mk (rationalNormOneSubgroup F G)
      (properParabolicNormOneInclusion F G hPD hG P n))
  simpa only [LeftCosetSpace.rightTranslate_mk, positiveQuotientHomeomorph_mk,
    Subgroup.coe_mul, properParabolicNormOneInclusion, AdelicSubgroupPoints.normOneInclusion_val]
    using h.symm

/-- For an existing continuous representative, full almost-everywhere cuspidality
is equivalent to vanishing of the canonical constant terms at every adelic point. -/
def GroupSchemeFullAEL2ContinuousCuspidalityStatement : Prop :=
  ∀ (f : C(Q, ℂ)) (φ : Lp ℂ 2 μQ), (φ : Q → ℂ) =ᵐ[μQ] f →
    (φ ∈ fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc ↔
      positiveQuotientContinuousPullback F G T i f ∈
        normalizedParabolicCuspidalSubrepresentation F G hPD hG)

/-- Promote almost-everywhere vanishing to pointwise vanishing by continuity and full
support of norm-one Haar measure. -/
theorem groupSchemeFullAEL2ContinuousCuspidality :
    GroupSchemeFullAEL2ContinuousCuspidalityStatement F G hPD hG T i hi I e hc := by
  intro f φ hf
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  have hAE := mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
    φ f (Lp.stronglyMeasurable φ) f.continuous.stronglyMeasurable hf
  change (φ : Q → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i ↔ _
  refine hAE.trans ⟨?_, ?_⟩
  · intro h
    apply (mem_normalizedParabolicCuspidalSubrepresentation_iff F G hPD hG _).2
    intro P a
    rw [positiveQuotientConstantTerm_normOneProjection F G hPD hG T i hi I e hc]
    have hcont : Continuous (properParabolicPositivePeriod F G hPD hG T i P f) := by
      rw [funext (properParabolicPositivePeriod_eq_constantTerm F G hPD hG T i P f)]
      exact (continuous_normalizedParabolicConstantTerm F G hPD hG P _).comp continuous_subtype_val
    have hzero := (show (∀ P : ProperRationalParabolic G,
      (∀ᵐ g ∂μG₁, HasConvergentProperParabolicPositivePeriod F G hPD hG T i P f g) ∧
      properParabolicPositivePeriod F G hPD hG T i P f =ᵐ[μG₁] 0) from h) P
    exact congrFun (Measure.eq_of_ae_eq hzero.2 hcont continuous_const) _
  · intro h
    exact mem_aeParabolicCuspidalFunctionSubmodule_of_continuous F G hPD hG T i f h

end Langlands.Automorphic.GroupSchemeFunctions
