import Langlands.Global.LeftCosetCompactFactorUnfolding
import Langlands.Global.LeftCosetSemidirectPeriod
import Langlands.Global.AdelicIwasawaCompatibleMeasureReduction
import Langlands.Global.AdelicIntertwiningStabilizer
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.Global.EisensteinConstantTerm.QuotientUnfolding
import Langlands.Global.EisensteinConstantTerm.Core

/-! # Iwasawa coordinates for unfolding a discrete parabolic subgroup -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set
open scoped CategoryTheory.MonObj ENNReal NNReal CompactlySupported

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme EisensteinConstantTerm
open InducedInnerProductIntegrable (parameterPower_mul continuous_parameterPower)

namespace ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)

local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
local notation "iG" => (ContinuousMonoidHom.toMonoidHom (map F P G p))
local notation "inclM" => (ContinuousMonoidHom.toMonoidHom (map F M P l))
local notation "Gₐ" => AdelicGroupPoints F G
local notation "Pₐ" => AdelicGroupPoints F P
local notation "Mₐ" => AdelicGroupPoints F M
local notation "Uₐ" => AdelicGroupPoints F U

/-- The image of the adelic radical, included in the adelic parabolic. -/
def radicalInclusion : N →* Pₐ :=
  (map F U P iU).toMonoidHom.comp
    (rangeEquiv F (iU ≫ p) (isClosedEmbedding_map F U G (iU ≫ p)).isEmbedding).symm.toMonoidHom

@[simp] theorem map_radicalInclusion (u : N) : iG (radicalInclusion p iU u) = u.val := by
  change map F P G p (map F U P iU _) = u.val
  rw [← map_comp_apply_of_hom iU]
  exact map_rangeEquiv_symm F (iU ≫ p) (isClosedEmbedding_map F U G (iU ≫ p)).isEmbedding u

theorem continuous_radicalInclusion : Continuous (radicalInclusion p iU) :=
  (map F U P iU).continuous.comp (rangeEquiv F (iU ≫ p)
    (isClosedEmbedding_map F U G (iU ≫ p)).isEmbedding).symm.continuous

theorem isEmbedding_radicalInclusion : IsEmbedding (radicalInclusion p iU) := by
  apply ((isClosedEmbedding_map F P G p).isEmbedding.of_comp_iff).mp
  have h : (map F P G p) ∘ (radicalInclusion p iU) = (Subtype.val : N → Gₐ) :=
    funext (map_radicalInclusion p iU)
  rw [h]
  exact IsEmbedding.subtypeVal

variable [IsIso (subgroupMultiplication l iU)]
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)

set_option quotPrecheck false in
local notation "proj" => (ContinuousMonoidHom.toMonoidHom (map F P M (leviRetraction l iU hU.1.isNormal)))

private theorem proj_inclM (m : Mₐ) : proj (inclM m) = m := by
  change map F P M (leviRetraction l iU hU.1.isNormal) (map F M P l m) = m
  rw [← map_comp_apply_of_hom l, levi_comp_leviRetraction]
  rfl

private theorem proj_eq_one_iff (x : Pₐ) :
    proj x = 1 ↔ ∃ n : N, radicalInclusion p iU n = x := by
  refine (comp_leviRetraction_eq_one_iff l iU hU.1.isNormal x).trans ?_
  constructor
  · rintro ⟨u, rfl⟩
    let v := rangeEquiv F (iU ≫ p) (isClosedEmbedding_map F U G (iU ≫ p)).isEmbedding
    refine ⟨v u, ?_⟩
    change map F U P iU (v.symm (v u)) = _
    exact congrArg (map F U P iU) (v.symm_apply_apply (show Uₐ from u))
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩

/-- Multiplication in radical-first order gives topological coordinates on the parabolic. -/
def coordinates : N × Mₐ ≃ₜ Pₐ :=
  LeftCosetSpace.Semidirect.prodHomeomorph (radicalInclusion p iU) inclM proj
    (proj_inclM iU l hU) (fun x hx => (proj_eq_one_iff p iU l hU x).mp hx)
    (fun n => (proj_eq_one_iff p iU l hU _).mpr ⟨n, rfl⟩)
    (isEmbedding_radicalInclusion p iU) (map F M P l).continuous
    (map F P M (leviRetraction l iU hU.1.isNormal)).continuous

@[simp] theorem coordinates_apply (x : N × Mₐ) :
    coordinates p iU l hU x = radicalInclusion p iU x.1 * inclM x.2 := rfl

theorem map_coordinates (x : N × Mₐ) :
    iG (coordinates p iU l hU x) = x.1.val * iG (inclM x.2) := by
  rw [coordinates_apply, map_mul, map_radicalInclusion]

/-- A point in the parabolic and in the ambient principal subgroup lifts to a principal
parabolic point. -/
theorem mem_rationalSubgroup_of_map (x : Pₐ)
    (hx : iG x ∈ rationalSubgroup F G) : x ∈ rationalSubgroup F P := by
  obtain ⟨d, hd⟩ := hx
  have hmem : rational F G d ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range p) := by
    rw [hd]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (rational_mem_adelicPoints_range_iff
    (inferInstance : IsClosedImmersion p.hom.hom.left) d).mp hmem
  refine ⟨y, (isClosedEmbedding_map F P G p).injective ?_⟩
  exact (map_rational p (show RationalGroupPoints F P from y)).trans
    ((congrArg (rational F G) hy).trans hd)

/-- The positive Iwasawa density on the Levi. -/
def inverseModulus (m : Mₐ) : ℝ :=
  ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖

theorem continuous_inverseModulus : Continuous (inverseModulus l) :=
  ((continuous_parameterPower _).comp (map F M P l).continuous).norm

theorem ofReal_inverseModulus (m : Mₐ) :
    (inverseModulus l m : ℂ) = parameterPower F P (-modulusParameter F P) (map F M P l m) := by
  rw [inverseModulus, IwasawaCompatibleMeasure.parameterPower_neg_modulusParameter,
    ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _))]

theorem inverseModulus_rational_mul (d : RationalGroupPoints F M) (m : Mₐ) :
    inverseModulus l (rational F M d * m) = inverseModulus l m := by
  unfold inverseModulus
  rw [map_mul, map_rational, parameterPower_mul]
  simp only [parameterPower, characterLog_rational, map_zero, Complex.exp_zero, one_mul]

variable (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]

local notation "dμM" => (Measure.withDensity μM
  (fun m => ENNReal.ofReal (inverseModulus l m)))

private theorem measurePreserving_inverseModulus_mul_left (d : RationalGroupPoints F M) :
    MeasurePreserving (fun m => rational F M d * m) dμM dμM := by
  let t := (Homeomorph.mulLeft (rational F M d)).toMeasurableEquiv
  have ht : MeasurePreserving t μM μM := measurePreserving_mul_left μM _
  have hme : Measurable (fun m : Mₐ => ENNReal.ofReal (inverseModulus l m)) :=
    ENNReal.measurable_ofReal.comp (continuous_inverseModulus l).measurable
  refine ⟨ht.measurable, ?_⟩
  ext S hS
  change Measure.map t dμM S = dμM S
  rw [Measure.map_apply ht.measurable hS, withDensity_apply _ (ht.measurable hS), withDensity_apply _ hS,
    ← ht.setLIntegral_comp_preimage_emb t.measurableEmbedding
      (fun m => ENNReal.ofReal (inverseModulus l m)) S]
  exact lintegral_congr (fun m => congrArg ENNReal.ofReal
    (inverseModulus_rational_mul l d m).symm)

local notation "S" => (SubgroupFunctor.range (iU ≫ p))

variable [hN : IsClosed (AdelicSubgroupPoints.adelicPoints F G
  (SubgroupFunctor.range (iU ≫ p)) : Set (AdelicGroupPoints F G))]

local instance : LocallyCompactSpace N := hN.locallyCompactSpace
local instance : PolishSpace N := hN.polishSpace
local notation "μN" => (AdelicSubgroupPoints.normalizedHaarMeasure F G S)

private theorem measurePreserving_radicalConj (d : RationalGroupPoints F P) :
    MeasurePreserving (conjAdelic p iU hU.1.isNormal (rational F P d)) μN μN := by
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G S) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ p)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G S
  let hΓ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G S
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure Γ hΓ) :=
    AdelicSubgroupPoints.rationalQuotientHaarMeasure_isFiniteMeasure F G S
  exact measurePreserving_of_preserves Γ (LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ)
    (LeftCosetSpace.fundamentalDomain_unique Γ hΓ) _
    (conjAdelic_mem_rationalSubgroup_iff p iU hU.1.isNormal d) Measure.haar
    (LeftCosetSpace.haar_fundamentalDomain_ne_zero Γ hΓ)
    (LeftCosetSpace.haar_fundamentalDomain_ne_top Γ hΓ) _

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))

local notation "μK" => (compactHaarProbability F G K hKc)

include hU in
set_option maxHeartbeats 900000 in
/-- The Iwasawa pushforward with the exact compatible Levi measure. -/
theorem map_iwasawaProduct
    (hμM : IsIwasawaCompatibleMeasure K hKc p iU l μM) :
    Measure.map (fun z : (N × Mₐ) × K => z.1.1.val * iG (inclM z.1.2) * z.2.val)
      ((Measure.prod μN dμM).prod μK) = (Measure.haar : Measure Gₐ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set Gₐ))
  let : IsLocallyFiniteMeasure dμM := IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_inverseModulus l)
  let : IsLocallyFiniteMeasure μN := Measure.isLocallyFiniteMeasure_smul Measure.haar
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G S)
  let : SFinite μN := inferInstanceAs (SFinite (AdelicSubgroupPoints.quotientMassNormalizer F G S •
    (Measure.haar : Measure N)))
  let : SFinite dμM := inferInstanceAs (SFinite (Measure.withDensity μM _))
  have h : ∀ (f : C_c(Gₐ, ℝ)),
      ∫ g, f g ∂(Measure.haar : Measure Gₐ) =
        ∫ k : K, ∫ x : N × Mₐ, f (iG (coordinates p iU l hU x) * k.val)
          ∂(Measure.prod μN dμM) ∂μK := by
    intro f
    let fC : C_c(Gₐ, ℂ) := ⟨⟨fun g => (f g : ℂ),
      Complex.continuous_ofReal.comp f.continuous⟩, f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
    have hF := hμM fC
    simp only [fC, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
      ← ofReal_inverseModulus l, ← Complex.ofReal_mul, integral_complex_ofReal] at hF
    have hF' := Complex.ofReal_injective hF
    refine hF'.trans (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_))
    have hE : IsClosedEmbedding (fun x : N × Mₐ => iG (coordinates p iU l hU x) * k.val) :=
      (Homeomorph.mulRight k.val).isClosedEmbedding.comp
        ((isClosedEmbedding_map F P G p).comp (coordinates p iU l hU).isClosedEmbedding)
    have hI : Integrable (fun x : N × Mₐ => f (iG (coordinates p iU l hU x) * k.val))
        (Measure.prod μN dμM) :=
      (f.continuous.comp hE.continuous).integrable_of_hasCompactSupport
        (f.hasCompactSupport.comp_isClosedEmbedding hE)
    dsimp only
    have hd : Measurable (fun m : Mₐ => ENNReal.ofReal (inverseModulus l m)) :=
      ENNReal.measurable_ofReal.comp (continuous_inverseModulus l).measurable
    rw [integral_prod_symm _ hI, integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [map_coordinates, smul_eq_mul]
    simp_rw [integral_const_mul]
    simp [inverseModulus]
  have hMap := map_compactFactor_eq_of_integral (map F P G p) (isClosedEmbedding_map F P G p)
    (coordinates p iU l hU) (Subtype.val : K → Gₐ) continuous_subtype_val
    Measure.haar (Measure.prod μN dμM) μK h
  rw [← hMap]
  congr 1
  funext z
  exact congrArg (fun y : Gₐ => y * z.2.val) (map_coordinates p iU l hU z.1).symm

theorem proj_coordinates (x : N × Mₐ) : proj (coordinates p iU l hU x) = x.2 := by
  rw [coordinates_apply, map_mul, (proj_eq_one_iff p iU l hU _).2 ⟨x.1, rfl⟩,
    proj_inclM iU l hU, one_mul]

private def parabolicMeasure : Measure Pₐ :=
  Measure.map (coordinates p iU l hU) (Measure.prod μN dμM)

private theorem measurePreserving_parabolicMeasure_rational_mul (d : RationalGroupPoints F P) :
    MeasurePreserving (fun x : Pₐ => rational F P d * x)
      (parabolicMeasure p iU l hU μM) (parabolicMeasure p iU l hU μM) := by
  let e := coordinates p iU l hU
  let x₀ := e.symm (rational F P d)
  let dM := P.affinePointsTarget (leviRetraction l iU hU.1.isNormal) _ d
  have hm₀ : x₀.2 = rational F M dM := by
    rw [← proj_coordinates p iU l hU x₀, show e x₀ = rational F P d from e.apply_symm_apply _,
      show proj (rational F P d) = rational F M dM from map_rational _ d]
  let α := conjAdelic p iU hU.1.isNormal (map F M P l x₀.2)
  have hα : MeasurePreserving α μN μN := by
    change MeasurePreserving (conjAdelic p iU hU.1.isNormal (map F M P l x₀.2)) μN μN
    rw [hm₀, map_rational]
    exact measurePreserving_radicalConj p iU hU _
  let : (μN).IsMulLeftInvariant := by unfold AdelicSubgroupPoints.normalizedHaarMeasure; infer_instance
  let : SFinite μN := inferInstanceAs (SFinite (AdelicSubgroupPoints.quotientMassNormalizer F G S •
    (Measure.haar : Measure N)))
  let : SFinite dμM := inferInstanceAs (SFinite (Measure.withDensity μM _))
  have htrans : MeasurePreserving (fun x : N × Mₐ => (x₀.1 * α x.1, x₀.2 * x.2))
      (Measure.prod μN dμM) (Measure.prod μN dμM) := by
    rw [show (fun x : N × Mₐ => (x₀.1 * α x.1, x₀.2 * x.2)) =
      Prod.map (fun n => x₀.1 * α n) (fun m => x₀.2 * m) from rfl]
    apply ((measurePreserving_mul_left μN x₀.1).comp hα).prod
    rw [hm₀]
    exact measurePreserving_inverseModulus_mul_left l μM dM
  have hcomm (x : N × Mₐ) : rational F P d * e x = e (x₀.1 * α x.1, x₀.2 * x.2) := by
    apply (isClosedEmbedding_map F P G p).injective
    rw [← show e x₀ = rational F P d from e.apply_symm_apply _, map_mul]
    change iG (coordinates p iU l hU x₀) * iG (coordinates p iU l hU x) =
      iG (coordinates p iU l hU (x₀.1 * α x.1, x₀.2 * x.2))
    rw [map_coordinates, map_coordinates, map_coordinates]
    simp only [map_mul inclM, map_mul iG]
    change (x₀.1.val * iG (inclM x₀.2)) * (x.1.val * iG (inclM x.2)) =
      x₀.1.val * (iG (inclM x₀.2) * x.1.val * (iG (inclM x₀.2))⁻¹) *
        (iG (inclM x₀.2) * iG (inclM x.2))
    group
  refine ⟨measurable_const_mul _, ?_⟩
  change Measure.map (fun x : Pₐ => rational F P d * x)
    (Measure.map e (Measure.prod μN dμM)) = Measure.map e (Measure.prod μN dμM)
  rw [Measure.map_map (measurable_const_mul _) e.continuous.measurable,
    show (fun x : Pₐ => rational F P d * x) ∘ e =
      e ∘ (fun x : N × Mₐ => (x₀.1 * α x.1, x₀.2 * x.2)) from funext hcomm,
    ← Measure.map_map e.continuous.measurable htrans.measurable, htrans.map_eq]

/-- The parabolic projection preserves principal membership. -/
theorem proj_mem_rationalSubgroup {x : Pₐ} (hx : x ∈ rationalSubgroup F P) :
    proj x ∈ rationalSubgroup F M := by
  obtain ⟨d, rfl⟩ := hx
  exact ⟨_, (map_rational (leviRetraction l iU hU.1.isNormal) d).symm⟩

include hU in
set_option maxHeartbeats 1000000 in
/-- The counting-normalized quotient of the compatible Iwasawa formula. -/
theorem map_iwasawaDiscreteProduct (hμM : IsIwasawaCompatibleMeasure K hKc p iU l μM)
    (Γ : Subgroup Gₐ) (hΓr : Γ ≤ rationalSubgroup F G) (hΓp : Γ ≤ MonoidHom.range iG)
    (hLevi : ∀ m ∈ rationalSubgroup F M, iG (inclM m) ∈ Γ)
    (Δ : Subgroup N) (hΔ : ∀ u : N, u ∈ Δ ↔ u.val ∈ Γ) :
    let hΓ := (isDiscrete_rationalSubgroup F G).mono hΓr
    let hΔd := (isDiscrete_rationalSubgroup F G).preimage continuous_subtype_val.continuousOn
      (Subtype.val_injective : Function.Injective (Subtype.val : N → Gₐ))
    let Dn := LeftCosetSpace.fundamentalDomain Δ (hΔd.mono (fun u hu => hΓr ((hΔ u).1 hu)))
    let Dm := LeftCosetSpace.fundamentalDomain (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M)
    LeftCosetSpace.discreteQuotientMeasure Γ hΓ (Measure.haar : Measure Gₐ) =
      Measure.map (fun z : (N × Mₐ) × K => LeftCosetSpace.mk Γ (z.1.1.val * iG (inclM z.1.2) * z.2.val))
        ((Measure.prod (Measure.restrict μN Dn) (Measure.restrict dμM Dm)).prod μK) := by
  intro hΓ hΔd Dn Dm
  let ΓP := Γ.comap iG
  let e := coordinates p iU l hU
  let ν := parabolicMeasure p iU l hU μM
  have hΓmap : ΓP.map iG = Γ := Subgroup.map_comap_eq_self hΓp
  have hΔeq : ΓP.comap (radicalInclusion p iU) = Δ := by
    ext u
    change iG (radicalInclusion p iU u) ∈ Γ ↔ u ∈ Δ
    rw [map_radicalInclusion, hΔ]
  have hn : IsDiscrete (ΓP.comap (radicalInclusion p iU) : Set N) := by
    rw [hΔeq]
    exact hΔd.mono (fun u hu => hΓr ((hΔ u).1 hu))
  have hpr : ∀ x ∈ ΓP, proj x ∈ rationalSubgroup F M := fun x hx =>
    proj_mem_rationalSubgroup iU l hU (mem_rationalSubgroup_of_map p x (hΓr hx))
  let D := e '' (Dn ×ˢ Dm)
  have hE : MeasurableSet (Dn ×ˢ Dm) := (LeftCosetSpace.measurableSet_fundamentalDomain _ _).prod
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
  have hD : MeasurableSet D := e.toMeasurableEquiv.measurableEmbedding.measurableSet_image' hE
  have huniq : ∀ x : Pₐ, ∃! d : ΓP, (d : Pₐ) * x ∈ D := by
    intro x
    have h := LeftCosetSpace.Semidirect.productFundamentalDomain_unique
      (radicalInclusion p iU) inclM proj (proj_inclM iU l hU)
      (fun x hx => (proj_eq_one_iff p iU l hU x).mp hx)
      (fun u => (proj_eq_one_iff p iU l hU _).mpr ⟨u, rfl⟩)
      (isEmbedding_radicalInclusion p iU) (map F M P l).continuous
      (map F P M (leviRetraction l iU hU.1.isNormal)).continuous ΓP (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) hLevi hpr hn x
    have hD' : LeftCosetSpace.fundamentalDomain (ΓP.comap (radicalInclusion p iU)) hn = Dn := by
      unfold Dn
      congr
    simpa only [hD', D, Dm, e, coordinates] using h
  let : SFinite μN := inferInstanceAs (SFinite (AdelicSubgroupPoints.quotientMassNormalizer F G S •
    (Measure.haar : Measure N)))
  let : SFinite dμM := inferInstanceAs (SFinite (Measure.withDensity μM _))
  let : SFinite ν := inferInstanceAs (SFinite (Measure.map e (Measure.prod μN dμM)))
  let : SMulInvariantMeasure ΓP Pₐ ν := ⟨fun d T hT => by
    obtain ⟨x, hx⟩ := mem_rationalSubgroup_of_map p d.val (hΓr d.property)
    have hd := measurePreserving_parabolicMeasure_rational_mul p iU l hU μM x
    change ν ((fun x : Pₐ => d.val * x) ⁻¹' T) = ν T
    simpa only [hx] using hd.measure_preimage hT.nullMeasurableSet⟩
  let mult := fun z : Pₐ × K => iG z.1 * z.2.val
  have hm : Measurable mult := by
    exact ((map F P G p).continuous.comp continuous_fst |>.mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hprod (ω : Measure (N × Mₐ)) : (Measure.map e ω).prod μK =
      Measure.map (Prod.map e (id : K → K)) (ω.prod μK) := by
    simpa only [Measure.map_id] using Measure.map_prod_map ω μK e.continuous.measurable
      (measurable_id (α := K))
  have hpull : Measure.map mult (ν.prod μK) = (Measure.haar : Measure Gₐ) := by
    change Measure.map mult ((Measure.map e (Measure.prod μN dμM)).prod μK) = _
    rw [hprod, Measure.map_map hm (e.continuous.measurable.prodMap measurable_id)]
    have heq : mult ∘ Prod.map e id = fun z : (N × Mₐ) × K => z.1.1.val * iG (inclM z.1.2) * z.2.val := by
      funext z
      exact congrArg (fun y : Gₐ => y * z.2.val) (map_coordinates p iU l hU z.1)
    rw [heq]
    exact map_iwasawaProduct p iU l hU μM hKc hμM
  have hQ := LeftCosetSpace.discreteQuotientMeasure_map_mul_prod iG
    (isClosedEmbedding_map F P G p).injective (map F P G p).continuous.measurable
    (Subtype.val : K → Gₐ) continuous_subtype_val.measurable ΓP Γ hΓ Measure.haar ν μK hΓmap hpull hD huniq
  have hν : ν.restrict D = Measure.map e (Measure.prod (Measure.restrict μN Dn) (Measure.restrict dμM Dm)) := by
    change (Measure.map e (Measure.prod μN dμM)).restrict D = _
    rw [Measure.restrict_map e.continuous.measurable hD,
      show e ⁻¹' D = Dn ×ˢ Dm from e.preimage_image _, ← Measure.prod_restrict]
  rw [hν, hprod] at hQ
  change _ = Measure.map (LeftCosetSpace.mk Γ ∘ mult) _ at hQ
  rw [Measure.map_map ((LeftCosetSpace.measurable_mk _).comp hm)
      (e.continuous.measurable.prodMap measurable_id)] at hQ
  convert hQ using 2
  funext z
  exact congrArg (fun y : Gₐ => LeftCosetSpace.mk Γ (y * z.2.val)) (map_coordinates p iU l hU z.1).symm

end ParabolicIwasawaMeasure

end Langlands.Global.AdelicGroupPoints
