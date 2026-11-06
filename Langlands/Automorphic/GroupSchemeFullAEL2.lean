import Langlands.Automorphic.GroupSchemeParabolicL2Period
import Langlands.Analysis.Local.QuotientPeriodAEEqProof

/-! # The full almost-everywhere cuspidal L2 subrepresentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.QuotientIntegration

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "μG" => (Measure.haar : Measure (normOneSubgroup F G))

/-- On specified functions, the actual radical period integrand is complex linear. -/
def properParabolicPositivePeriodIntegrandLinear (P : ProperRationalParabolic G)
    (g : normOneSubgroup F G) :
    (Q → ℂ) →ₗ[ℂ]
      (AdelicSubgroupPoints.RationalQuotient F G (properRationalParabolicRadicals hPD hG P) → ℂ) where
  toFun φ := properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g
  map_add' φ ψ := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n =>
      change properParabolicPositivePeriodIntegrand F G hPD hG T i P (φ + ψ) g
        (LeftCosetSpace.mk _ n) =
          properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g
            (LeftCosetSpace.mk _ n) +
          properParabolicPositivePeriodIntegrand F G hPD hG T i P ψ g
            (LeftCosetSpace.mk _ n)
      simp only [properParabolicPositivePeriodIntegrand_mk, Pi.add_apply]
  map_smul' z φ := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n =>
      change properParabolicPositivePeriodIntegrand F G hPD hG T i P (z • φ) g
        (LeftCosetSpace.mk _ n) =
          z • properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g
            (LeftCosetSpace.mk _ n)
      simp only [properParabolicPositivePeriodIntegrand_mk, Pi.smul_apply]

theorem properParabolicPositivePeriodIntegrand_zero (P : ProperRationalParabolic G)
    (g : normOneSubgroup F G) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P (0 : Q → ℂ) g = 0 :=
  (properParabolicPositivePeriodIntegrandLinear F G hPD hG T i P g).map_zero

theorem properParabolicPositivePeriodIntegrand_add (P : ProperRationalParabolic G)
    (φ ψ : Q → ℂ) (g : normOneSubgroup F G) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P (φ + ψ) g =
      properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g +
        properParabolicPositivePeriodIntegrand F G hPD hG T i P ψ g :=
  (properParabolicPositivePeriodIntegrandLinear F G hPD hG T i P g).map_add φ ψ

theorem properParabolicPositivePeriodIntegrand_smul (P : ProperRationalParabolic G)
    (z : ℂ) (φ : Q → ℂ) (g : normOneSubgroup F G) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P (z • φ) g =
      z • properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g :=
  (properParabolicPositivePeriodIntegrandLinear F G hPD hG T i P g).map_smul z φ

/-- Separate AE convergence and vanishing, on raw specified functions before null classes.
No measurability or L2 condition on the input is part of this auxiliary carrier. -/
def aeParabolicCuspidalFunctionSubmodule : Submodule ℂ (Q → ℂ) where
  carrier := {φ | ∀ P : ProperRationalParabolic G,
    (∀ᵐ g ∂μG, HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
    properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[μG] 0}
  zero_mem' := by
    intro P
    constructor
    · filter_upwards with g
      change Integrable _ _
      rw [properParabolicPositivePeriodIntegrand_zero]
      exact integrable_zero _ _ _
    · filter_upwards with g
      change (∫ q, properParabolicPositivePeriodIntegrand F G hPD hG T i P 0 g q
        ∂properParabolicQuotientMeasure F G hPD hG P) = 0
      rw [properParabolicPositivePeriodIntegrand_zero]
      exact integral_zero _ _
  add_mem' := by
    intro φ ψ hφ hψ P
    obtain ⟨hφc, hφv⟩ := hφ P
    obtain ⟨hψc, hψv⟩ := hψ P
    have hc : ∀ᵐ g ∂μG,
        HasConvergentProperParabolicPositivePeriod F G hPD hG T i P (φ + ψ) g := by
      filter_upwards [hφc, hψc] with g hg hk
      change Integrable _ _
      rw [properParabolicPositivePeriodIntegrand_add]
      exact hg.add hk
    refine ⟨hc, ?_⟩
    filter_upwards [hφc, hψc, hφv, hψv] with g hg hk hgv hkv
    change (∫ q, properParabolicPositivePeriodIntegrand F G hPD hG T i P (φ + ψ) g q
      ∂properParabolicQuotientMeasure F G hPD hG P) = 0
    simp only [properParabolicPositivePeriodIntegrand_add, Pi.add_apply]
    rw [integral_add hg hk]
    change properParabolicPositivePeriod F G hPD hG T i P φ g +
      properParabolicPositivePeriod F G hPD hG T i P ψ g = 0
    simp only [hgv, hkv, Pi.zero_apply, add_zero]
  smul_mem' := by
    intro z φ hφ P
    obtain ⟨hφc, hφv⟩ := hφ P
    refine ⟨?_, ?_⟩
    · filter_upwards [hφc] with g hg
      change Integrable _ _
      rw [properParabolicPositivePeriodIntegrand_smul]
      exact hg.smul z
    · filter_upwards [hφv] with g hg
      change (∫ q, properParabolicPositivePeriodIntegrand F G hPD hG T i P (z • φ) g q
        ∂properParabolicQuotientMeasure F G hPD hG P) = 0
      simp only [properParabolicPositivePeriodIntegrand_smul, Pi.smul_apply]
      rw [integral_smul]
      change z • properParabolicPositivePeriod F G hPD hG T i P φ g = 0
      simp only [hg, Pi.zero_apply, smul_zero]

variable (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

include hi I e hc in
/-- Actual canonical periods respect AE equality of specified strongly measurable functions. -/
theorem properParabolicPositivePeriod_congr_ae (P : ProperRationalParabolic G)
    (φ ψ : Q → ℂ) (hφ : StronglyMeasurable φ) (hψ : StronglyMeasurable ψ)
    (heq : φ =ᵐ[μQ] ψ) :
    ∀ᵐ g ∂μG,
      (HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g ↔
        HasConvergentProperParabolicPositivePeriod F G hPD hG T i P ψ g) ∧
      properParabolicPositivePeriod F G hPD hG T i P φ g =
        properParabolicPositivePeriod F G hPD hG T i P ψ g := by
  let mp := measurePreserving_positiveQuotient F G T i hi I e hc
  have hφ' := hφ.comp_measurable mp.measurable
  have hψ' := hψ.comp_measurable mp.measurable
  have heq' := mp.quasiMeasurePreserving.ae_eq_comp heq
  have h := quotientPeriodAEEq
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G) μG
    (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _)
    Measure.haar (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom
    (properParabolicNormOneInclusion F G hPD hG P).continuous
    (properParabolicNormOneInclusion_rational_mem F G hPD hG P)
    1 continuous_const (fun _ => rfl) _ _ hφ' hψ' heq'
  filter_upwards [h] with g hg
  refine ⟨?_, ?_⟩
  · change Integrable _ _ ↔ Integrable _ _
    rw [properParabolicQuotientMeasure,
      AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_eq_normalizedMeasure]
    exact hg.2.1
  · rw [properParabolicPositivePeriod_eq_normalizedPeriod,
      properParabolicPositivePeriod_eq_normalizedPeriod]
    exact hg.2.2

include hi I e hc in
/-- The auxiliary convergence-and-vanishing condition descends to actual null classes. -/
theorem mem_aeParabolicCuspidalFunctionSubmodule_congr
    (φ ψ : Q → ℂ) (hφ : StronglyMeasurable φ) (hψ : StronglyMeasurable ψ)
    (heq : φ =ᵐ[μQ] ψ) :
    φ ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i ↔
      ψ ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i := by
  have transfer (a b : Q → ℂ) (ha : StronglyMeasurable a) (hb : StronglyMeasurable b)
      (hab : a =ᵐ[μQ] b)
      (hm : a ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i) :
      b ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i := by
    intro P
    have h := properParabolicPositivePeriod_congr_ae F G hPD hG T i hi I e hc P a b ha hb hab
    refine ⟨?_, ?_⟩
    · filter_upwards [(hm P).1, h] with g hg hh
      exact hh.1.mp hg
    · filter_upwards [(hm P).2, h] with g hg hh
      exact hh.2.symm.trans hg
  exact ⟨transfer φ ψ hφ hψ heq, transfer ψ φ hψ hφ heq.symm⟩

/-- The full existing AE cusp locus, with its actual complex submodule structure. -/
def fullAEL2CuspidalSubmodule : Submodule ℂ (Lp ℂ 2 μQ) where
  carrier := fullAEL2CuspidalLocus F G hPD hG T i
  zero_mem' := by
    apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
      (0 : Lp ℂ 2 μQ) 0 (Lp.stronglyMeasurable _) stronglyMeasurable_zero
      (Lp.coeFn_zero ℂ 2 μQ)).mpr
    exact (aeParabolicCuspidalFunctionSubmodule F G hPD hG T i).zero_mem
  add_mem' := by
    intro φ ψ hφ hψ
    apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
      (φ + ψ : Lp ℂ 2 μQ) ((φ : Q → ℂ) + (ψ : Q → ℂ))
      (Lp.stronglyMeasurable _) ((Lp.stronglyMeasurable φ).add (Lp.stronglyMeasurable ψ))
      (Lp.coeFn_add φ ψ)).mpr
    exact (aeParabolicCuspidalFunctionSubmodule F G hPD hG T i).add_mem hφ hψ
  smul_mem' := by
    intro z φ hφ
    apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
      (z • φ : Lp ℂ 2 μQ) (z • (φ : Q → ℂ))
      (Lp.stronglyMeasurable _) ((Lp.stronglyMeasurable φ).const_smul z)
      (Lp.coeFn_smul z φ)).mpr
    exact (aeParabolicCuspidalFunctionSubmodule F G hPD hG T i).smul_mem z hφ

@[simp]
theorem mem_fullAEL2CuspidalSubmodule (φ : Lp ℂ 2 μQ) :
    φ ∈ fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc ↔
      φ ∈ fullAEL2CuspidalLocus F G hPD hG T i := Iff.rfl

include hi I e hc in
/-- Positive pullback by any ambient element translates the actual period variable
by its norm-one projection. -/
theorem properParabolicPositivePeriodIntegrand_rightTranslate
    (P : ProperRationalParabolic G) (φ : Q → ℂ)
    (a : AdelicGroupPoints F G) (g : normOneSubgroup F G) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P
      (fun q => φ (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) a q)) g =
      properParabolicPositivePeriodIntegrand F G hPD hG T i P φ
        (g * normOneProjection F G T i hi I e hc a) := by
  funext q
  obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective
    (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P)) q
  rw [properParabolicPositivePeriodIntegrand_mk, properParabolicPositivePeriodIntegrand_mk]
  apply congrArg φ
  have h := positiveQuotientHomeomorph_rightTranslate F G T i hi I e hc a
    (LeftCosetSpace.mk (rationalNormOneSubgroup F G)
      (properParabolicNormOneInclusion F G hPD hG P n * g))
  simpa only [LeftCosetSpace.rightTranslate_mk, positiveQuotientHomeomorph_mk,
    Subgroup.coe_mul, properParabolicNormOneInclusion,
    AdelicSubgroupPoints.normOneInclusion_val, mul_assoc] using h.symm

include hi I e hc in
theorem properParabolicPositivePeriod_rightTranslate
    (P : ProperRationalParabolic G) (φ : Q → ℂ)
    (a : AdelicGroupPoints F G) (g : normOneSubgroup F G) :
    properParabolicPositivePeriod F G hPD hG T i P
      (fun q => φ (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) a q)) g =
      properParabolicPositivePeriod F G hPD hG T i P φ
        (g * normOneProjection F G T i hi I e hc a) := by
  unfold properParabolicPositivePeriod
  rw [properParabolicPositivePeriodIntegrand_rightTranslate F G hPD hG T i hi I e hc]

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi I e hc in
/-- Ambient norm-one right Haar invariance preserves the separate AE convergence
and vanishing requirements under every ambient positive right pullback. -/
theorem mem_aeParabolicCuspidalFunctionSubmodule_rightTranslate
    (a : AdelicGroupPoints F G) (φ : Q → ℂ)
    (hφ : φ ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i) :
    (fun q => φ (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) a q)) ∈
      aeParabolicCuspidalFunctionSubmodule F G hPD hG T i := by
  let mp := measurePreserving_mul_right μG (normOneProjection F G T i hi I e hc a)
  intro P
  refine ⟨?_, ?_⟩
  · filter_upwards [mp.quasiMeasurePreserving.ae (hφ P).1] with g hg
    change Integrable _ _
    rw [properParabolicPositivePeriodIntegrand_rightTranslate F G hPD hG T i hi I e hc]
    exact hg
  · filter_upwards [mp.quasiMeasurePreserving.ae (hφ P).2] with g hg
    change properParabolicPositivePeriod F G hPD hG T i P _ g = 0
    rw [properParabolicPositivePeriod_rightTranslate F G hPD hG T i hi I e hc]
    exact hg

/-- The entire original AE cusp locus is stable under the original positive
right representation on actual quotient L2 classes. -/
def fullAEL2CuspidalSubrepresentation :
    Subrepresentation (quotientL2RightAction F G T i μQ
      (haarQuotientMeasureRightInvariant F G T i hi I e hc)) where
  toSubmodule := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  apply_mem_toSubmodule a φ hφ := by
    let hR := haarQuotientMeasureRightInvariant F G T i hi I e hc
    change quotientL2RightTranslate F G T i μQ hR a φ ∈
      fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
      (quotientL2RightTranslate F G T i μQ hR a φ)
      (fun q => φ (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) a q))
      (Lp.stronglyMeasurable _) ((Lp.stronglyMeasurable φ).comp_measurable (hR a).measurable)
      (coeFn_quotientL2RightTranslate F G T i μQ hR a φ)).mpr
    exact mem_aeParabolicCuspidalFunctionSubmodule_rightTranslate F G hPD hG T i hi I e hc a φ hφ

/-- Positive right translation restricted to the full AE cuspidal submodule. -/
def fullAEL2CuspidalRightAction :
    Representation ℂ (AdelicGroupPoints F G)
      (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :=
  (fullAEL2CuspidalSubrepresentation F G hPD hG T i hi I e hc).toRepresentation

/-- The restricted action preserves the inherited L2 norm. -/
theorem norm_fullAEL2CuspidalRightAction (a : AdelicGroupPoints F G)
    (φ : fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    ‖fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc a φ‖ = ‖φ‖ := by
  exact (quotientL2RightTranslate F G T i μQ
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) a).norm_map φ.val

/-- The faithful inclusion intertwines the unchanged positive right actions. -/
def fullAEL2CuspidalToLp :
    (fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc).IntertwiningMap
      (quotientL2RightAction F G T i μQ
        (haarQuotientMeasureRightInvariant F G T i hi I e hc)) where
  toLinearMap := (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).subtype
  isIntertwining' _ := rfl

end Langlands.Automorphic.GroupSchemeFunctions
