import Langlands.Global.AdelicAdjunctionIwasawaUnfold
import Langlands.Global.AdelicAdjunctionRefold
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Global.AdelicInducedInnerProductGramCoordinateProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Compatible Iwasawa integration for a change of compact subgroup -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme Automorphic.GroupSchemeFunctions LeftCosetSpace
open InducedInnerProductIntegrable ParabolicIwasawaMeasure

namespace InducedPairingCompactChange

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)

local notation "Gₐ" => AdelicGroupPoints F G
local notation "Mₐ" => AdelicGroupPoints F M
local notation "mG" => (fun m => map F P G p (map F M P l m))

/-- The rational points in the adelic image of the parabolic. -/
def principalParabolic : Subgroup Gₐ :=
  rationalSubgroup F G ⊓ (map F P G p).toMonoidHom.range

theorem principalParabolic_discrete : IsDiscrete (principalParabolic p : Set Gₐ) :=
  (isDiscrete_rationalSubgroup F G).mono inf_le_left

/-- The quotient measure from the same ambient Haar measure for every choice of compact. -/
def principalParabolicMeasure : Measure (LeftCosetSpace (principalParabolic p)) :=
  discreteQuotientMeasure (principalParabolic p) (principalParabolic_discrete p) Measure.haar

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]

local notation "κ" => (compactHaarProbability F G K hKc)
local notation "ν" => (discreteQuotientMeasure (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) μM)

set_option maxHeartbeats 1000000 in
/-- For a left `U(𝔸) M(F)`-invariant integrand, the normalized radical quotient has
mass one. Refolding the Levi coordinate gives the compatible Iwasawa formula. -/
theorem quotientIwasawa [IsIso (subgroupMultiplication l iU)]
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hμM : IsIwasawaCompatibleMeasure K hKc p iU l μM)
    (f : Gₐ → ℂ) (hfc : Continuous f)
    (hf : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) f) :
    let W : K × RationalQuotient F M → ℂ := fun z =>
      (inverseModulus l z.2.out : ℂ) * f (mG z.2.out * z.1.val)
    (Integrable (fun z : LeftCosetSpace (principalParabolic p) => f z.out)
      (principalParabolicMeasure p) ↔ Integrable W ((κ).prod ν)) ∧
    (∫ z : LeftCosetSpace (principalParabolic p), f z.out ∂(principalParabolicMeasure p)) =
      ∫ z, W z ∂((κ).prod ν) := by
  intro W
  let S := SubgroupFunctor.range (iU ≫ p)
  let N := AdelicSubgroupPoints.adelicPoints F G S
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G S
  let hΔd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G S
  let Γ := principalParabolic p
  let : IsClosed (N : Set Gₐ) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  let : CompactSpace (LeftCosetSpace Δ) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ p)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let μN := AdelicSubgroupPoints.normalizedHaarMeasure F G S
  let μΔ := discreteQuotientMeasure Δ hΔd μN
  have hμΔ : μΔ = AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G S := by
    dsimp only [μΔ, μN, AdelicSubgroupPoints.normalizedHaarMeasure,
      AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
      AdelicSubgroupPoints.rationalQuotientHaarMeasure, haarQuotientMeasure, discreteQuotientMeasure,
      quotientMeasure]
    rw [Measure.restrict_smul, Measure.map_smul _ (measurable_mk Δ).aemeasurable]
  let : IsProbabilityMeasure μΔ := hμΔ.symm ▸
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G S
  have hΔ (u : N) : u ∈ Δ ↔ u.val ∈ Γ := by
    have huP : u.val ∈ (map F P G p).toMonoidHom.range := by
      obtain ⟨x, hx⟩ := u.property
      exact ⟨map F U P iU x, (map_comp_apply_of_hom iU x).symm.trans hx⟩
    exact (mem_adelicRadical_rational_iff iU u).trans (and_iff_left huP).symm
  have hLevi (m : Mₐ) (hm : m ∈ rationalSubgroup F M) : mG m ∈ Γ := by
    obtain ⟨x, rfl⟩ := hm
    refine ⟨?_, ⟨map F M P l (rational F M x), rfl⟩⟩
    change map F P G p (map F M P l (rational F M x)) ∈ rationalSubgroup F G
    rw [map_rational, map_rational]
    exact ⟨_, rfl⟩
  have hInv (g : Gₐ) (hg : g ∈ Γ) (x : Gₐ) : f (g * x) = f x :=
    hf g (mem_parabolicQuotientSubgroup_of_rational_range (p := p) iU l hU hg.1 hg.2) x
  obtain ⟨hi, he⟩ := unfoldDiscreteIwasawa p iU l hU hKc μM hμM Γ inf_le_left inf_le_right
    hLevi Δ hΔd hΔ f hfc hInv
  let Dm := fundamentalDomain (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M)
  let ν₀ := μM.restrict Dm
  let R : (LeftCosetSpace Δ × Mₐ) × K → K × RationalQuotient F M := fun z =>
    (z.2, mk (rationalSubgroup F M) z.1.2)
  have hR : MeasurePreserving R ((μΔ.prod ν₀).prod κ) ((κ).prod ν) := by
    have hmk : MeasurePreserving (mk (rationalSubgroup F M)) ν₀ ν :=
      ⟨measurable_mk _, rfl⟩
    have hforget : MeasurePreserving (Prod.snd : LeftCosetSpace Δ × Mₐ → Mₐ)
        (μΔ.prod ν₀) ν₀ := measurePreserving_snd
    exact ((MeasurePreserving.id κ).prod (hmk.comp hforget)).comp Measure.measurePreserving_swap
  have hW : Measurable W := by
    apply (continuous_out_of_invariant (rationalSubgroup F M)
      (fun (k : K) m => (inverseModulus l m : ℂ) * f (mG m * (k : Gₐ))) ?_ ?_).measurable
    · exact (Complex.continuous_ofReal.comp ((continuous_inverseModulus l).comp continuous_snd)).mul
        (hfc.comp (((map F P G p).continuous.comp ((map F M P l).continuous.comp continuous_snd)).mul
          (continuous_subtype_val.comp continuous_fst)))
    · intro k d hd m
      obtain ⟨x, rfl⟩ := hd
      dsimp only []
      rw [inverseModulus_rational_mul, map_mul, map_mul, mul_assoc, hInv _ (hLevi _ ⟨x, rfl⟩)]
  have hWr : unfoldedIntegrand (K := K) p iU l Δ f = W ∘ R := by
    funext z
    have hrad := hf (z.1.1.out : N).val (Subgroup.mem_sup_left (z.1.1.out : N).property)
      (mG z.1.2 * z.2.val)
    unfold unfoldedIntegrand
    rw [mul_assoc, hrad]
    change (inverseModulus l z.1.2 : ℂ) * f (mG z.1.2 * z.2.val) = _
    exact (out_mk_of_invariant (rationalSubgroup F M)
      (fun m => (inverseModulus l m : ℂ) * f (mG m * z.2.val))
      (fun d hd m => by
        obtain ⟨x, rfl⟩ := hd
        dsimp only []
        rw [inverseModulus_rational_mul, map_mul, map_mul, mul_assoc, hInv _ (hLevi _ ⟨x, rfl⟩)])
      z.1.2).symm
  rw [hWr] at hi he
  refine ⟨hi.trans ?_, he.trans ?_⟩
  · exact hR.integrable_comp hW.aestronglyMeasurable
  · change (∫ z, W (R z) ∂((μΔ.prod ν₀).prod κ)) = _
    rw [← hR.map_eq, integral_map hR.measurable.aemeasurable hW.aestronglyMeasurable]

section Weights

open InducedInnerProductSesquilinear PositiveRealTorus RestrictionSplitCentre

variable {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)

private theorem exists_central_coordinate (hl : IsRationalLeviSubgroup l) (y : Fin n → ℝ) :
    ∃ b : Mₐ, b ∈ canonicalSubgroup F M ∧ (∀ m : Mₐ, Commute b m) ∧
      parameterCoordinates F P e (characterLog F P (map F M P l b)) = y := by
  have hi := canonical_characterRestrict_injective F M centralSplitTorusCharacter
    hl.isConnectedReductive
  have := canonical_finiteIndex F M hl.isConnectedReductive
  have hs := isSplitComponent_canonicalComponent F M
  obtain ⟨I, hI, ⟨e₀⟩⟩ := hs.1.1.1
  let : Fintype I := Fintype.ofFinite I
  let E := InducedInnerProductGram.torusCoordinateHomeomorph l e (canonicalTorus F M)
    (canonicalComponent F M) hi I e₀ hl
  obtain ⟨a, ha⟩ := E.surjective y
  exact ⟨_, mem_canonicalSubgroup_positivePointMap a,
    positivePointMap_commute F M _ _ hs.1.2 a,
    (InducedInnerProductGram.torusCoordinateHomeomorph_apply l e _ _ hi I e₀ hl a).symm.trans ha⟩

private theorem halfModulus_star (x : AdelicGroupPoints F P) :
    starRingEnd ℂ (parameterPower F P (halfModulusParameter F P) x) =
      parameterPower F P (halfModulusParameter F P) x := by
  unfold parameterPower halfModulusParameter
  rw [complexParameterPairing_tmul, ← Complex.exp_conj]
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

/-- Translating the height weight leaves the pairing unchanged. A central point with the given
height shift translates the Levi quotient and the two half moduli cancel the inverse modulus. -/
theorem inducedInnerProduct_shift (hl : IsRationalLeviSubgroup l)
    (β : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) {φ ψ : Gₐ → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) ψ)
    (hφeq : IsSplitComponentEquivariant p l φ) (hψeq : IsSplitComponentEquivariant p l ψ) :
    inducedInnerProduct K hKc p l μM e (fun x => β (x + y)) φ ψ =
      inducedInnerProduct K hKc p l μM e β φ ψ := by
  obtain ⟨b, hb, hbcomm, hby⟩ := exists_central_coordinate l e hl y
  let : μM.IsMulRightInvariant := by
    let : (Measure.haar : Measure Mₐ).IsMulRightInvariant :=
      adelicHaarUnimodularity.2 F M hl.isConnectedReductive
    rw [Measure.isMulLeftInvariant_eq_smul μM (Measure.haar : Measure Mₐ)]
    infer_instance
  have ht := measurePreserving_rightTranslate_discrete (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M) μM b
  let Γ := rationalSubgroup F M
  let t := (rightTranslateHomeomorph Γ b).toMeasurableEquiv
  rw [inducedInnerProduct_eq_kernel, inducedInnerProduct_eq_kernel]
  apply integral_congr_ae
  filter_upwards with k
  let W := kernel p l e β φ ψ k.val
  change (∫ m : RationalQuotient F M, kernel p l e (fun x => β (x + y)) φ ψ k.val m.out ∂ν) =
    ∫ m : RationalQuotient F M, W m.out ∂ν
  rw [← ht.integral_comp t.measurableEmbedding (fun m : RationalQuotient F M => W m.out)]
  apply integral_congr_ae
  filter_upwards with m
  have htm : t m = mk Γ (m.out * b) := by
    change rightTranslate Γ b m = _
    exact congrArg (rightTranslate Γ b) (Quotient.out_eq m).symm
  have hφ₀ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ :=
    fun x hx g => hφ x (Subgroup.mem_sup_right hx) g
  have hψ₀ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) ψ :=
    fun x hx g => hψ x (Subgroup.mem_sup_right hx) g
  rw [show rightTranslate Γ b m = t m from rfl, htm,
    out_mk_of_invariant Γ W (fun x hx z => kernel_rational_mul e β hφ₀ hψ₀ hx k.val z),
    ← (hbcomm m.out).eq]
  have hheight : parameterCoordinates F P e (characterLog F P (map F M P l (b * m.out))) =
      parameterCoordinates F P e (characterLog F P (map F M P l m.out)) + y := by
    rw [map_mul, characterLog_mul, parameterCoordinates_add, hby, add_comm]
  have hmod : parameterPower F P (-modulusParameter F P) (map F M P l b) *
      (parameterPower F P (halfModulusParameter F P) (map F M P l b) *
        parameterPower F P (halfModulusParameter F P) (map F M P l b)) = 1 := by
    rw [← mul_assoc, ← parameterPower_add, ← parameterPower_add,
      neg_modulus_add_half_add_half, parameterPower_zero]
  dsimp only [W, InducedInnerProductSesquilinear.kernel, weight]
  rw [hheight, form_canonical_mul hφeq hb, form_canonical_mul hψeq hb,
    map_mul (starRingEnd ℂ), halfModulus_star, map_mul (map F M P l) b m.out, parameterPower_mul]
  linear_combination -((β (parameterCoordinates F P e (characterLog F P (map F M P l m.out)) + y) : ℂ) *
    parameterPower F P (-modulusParameter F P) (map F M P l m.out) *
    φ (mG m.out * k.val) * starRingEnd ℂ (ψ (mG m.out * k.val))) * hmod

set_option maxHeartbeats 800000 in
/-- A nonzero compactly supported height weight detects the square-integrability condition
on the canonical Levi quotient. -/
theorem integrable_normWeight_of_integrable_kernel (hl : IsRationalLeviSubgroup l)
    {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) {β : (Fin n → ℝ) → ℝ}
    (hβc : Continuous β) (hβs : HasCompactSupport β) (hβne : ∃ y, β y ≠ 0)
    {φ : Gₐ → ℂ} (hφc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hφeq : IsSplitComponentEquivariant p l φ)
    (hI : Integrable (fun z : K × RationalQuotient F M => kernel p l e β φ φ z.1 z.2.out)
      ((κ).prod ν)) :
    Integrable (fun z : K × CanonicalQuotient F M => normWeight p l φ z.1 z.2.out)
      ((κ).prod (canonicalMeasure F M)) := by
  by_cases hzero : φ = 0
  · subst φ
    simp [normWeight]
  have hφ₀ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ :=
    fun x hx g => hφ x (Subgroup.mem_sup_right hx) g
  have hM := hl.isConnectedReductive
  let := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  obtain ⟨C, hC, hEq⟩ := exists_lintegral_rationalQuotient_kernel e hM hlπ hβc hβs hφc hφ₀ hφeq
  let ν₁ := discreteQuotientMeasure (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) Measure.haar
  have hCpos : C ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := hβne
    obtain ⟨b, -, -, hby⟩ := exists_central_coordinate l e hl y
    obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
      by_contra! h
      exact hzero (funext h)
    let k := (mG b)⁻¹ * g
    let W := kernel p l e β φ φ k
    have hWc : Continuous (fun q : RationalQuotient F M => W q.out) :=
      continuous_out (rationalSubgroup F M) W
        (continuous_kernel p l e β continuous_const continuous_id hβc hφc hφc)
        (fun _ hx _ => kernel_rational_mul e β hφ₀ hφ₀ hx k _)
    have hZ : ∫⁻ q : RationalQuotient F M, ‖W q.out‖ₑ ∂ν₁ = 0 := by
      rw [hEq, h0, zero_mul]
    have hAE := (lintegral_eq_zero_iff hWc.enorm.measurable).mp hZ
    let : ν₁.IsOpenPosMeasure := isOpenPosMeasure_discreteQuotientMeasure _ _ _
    have he := (hWc.enorm.ae_eq_iff_eq ν₁ continuous_zero).mp hAE
    have heval := congrFun he (mk (rationalSubgroup F M) b)
    change ‖W (mk (rationalSubgroup F M) b).out‖ₑ = 0 at heval
    rw [out_mk_of_invariant _ W (fun _ hx _ => kernel_rational_mul e β hφ₀ hφ₀ hx k _),
      enorm_eq_zero] at heval
    have hpoint : map F P G p (map F M P l b) * k = g := mul_inv_cancel_left _ _
    dsimp only [W, InducedInnerProductSesquilinear.kernel, weight] at heval
    rw [hby, hpoint] at heval
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hy)
      (Complex.exp_ne_zero _)) hg) (by simpa using hg)) heval
  have hcont : Continuous (fun q : K × RationalQuotient F M => kernel p l e β φ φ q.1 q.2.out) :=
    continuous_prod_out (rationalSubgroup F M) (fun q : K × Mₐ => kernel p l e β φ φ q.1 q.2)
      (continuous_kernel p l e β continuous_fst.subtype_val continuous_snd hβc hφc hφc)
      (fun _ x hx m => kernel_rational_mul e β hφ₀ hφ₀ hx _ m)
  have hcont₂ : Continuous (fun q : K × CanonicalQuotient F M => normWeight p l φ q.1 q.2.out) :=
    continuous_prod_out (canonicalRationalSubgroup F M) (fun q : K × Mₐ => normWeight p l φ q.1 q.2)
      (continuous_normWeight p l continuous_fst.subtype_val continuous_snd hφc)
      (fun _ x hx m => canonicalRationalSubgroup_le_leftStabilizer hφ₀ hφeq _ hx m)
  let : SFinite ν₁ := sFinite_discreteQuotientMeasure Measure.haar
  let : SFinite (canonicalMeasure F M) := by
    unfold canonicalMeasure quotientHaarMeasure normOneRationalQuotientHaarMeasure
      haarQuotientMeasure discreteQuotientMeasure quotientMeasure
    infer_instance
  let c := Measure.haarScalarFactor μM (Measure.haar : Measure Mₐ)
  have hc : (c : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μM
      (Measure.haar : Measure Mₐ)).ne'
  have hν : ν = c • ν₁ := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μM (Measure.haar : Measure Mₐ)]
    simp only [ν₁, discreteQuotientMeasure, quotientMeasure, Measure.restrict_smul,
      Measure.map_smul _ (measurable_mk _).aemeasurable, c]
  rw [hν, Measure.prod_smul_right] at hI
  have hI₁ := (integrable_smul_measure hc ENNReal.coe_ne_top).mp hI
  have hfin := hI₁.hasFiniteIntegral
  unfold HasFiniteIntegral at hfin
  rw [lintegral_prod _ hcont.enorm.aemeasurable] at hfin
  rw [lintegral_congr (fun k : K => hEq k.val)] at hfin
  rw [lintegral_const_mul' _ _ hC.ne, ← lintegral_prod _ hcont₂.enorm.aemeasurable] at hfin
  refine ⟨hcont₂.aestronglyMeasurable, lt_top_iff_ne_top.mpr fun hh => ?_⟩
  exact hfin.ne (ENNReal.mul_eq_top.mpr (Or.inl ⟨hCpos, hh⟩))

end Weights

section Pairing

variable (hK : IsIwasawaCompact p K) {n : ℕ}
  (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)

/-- The product of two inducing functions weighted by the Iwasawa height on the parabolic
quotient. -/
def weightedProduct (φ ψ : Gₐ → ℂ) (g : Gₐ) : ℂ :=
  (β (hK.heightCoordinates e g) : ℂ) * φ g * starRingEnd ℂ (ψ g)

theorem continuous_weightedProduct {φ ψ : Gₐ → ℂ} (hβ : Continuous β)
    (hφ : Continuous φ) (hψ : Continuous ψ) : Continuous (weightedProduct p hK e β φ ψ) :=
  ((Complex.continuous_ofReal.comp (hβ.comp (hK.continuous_heightCoordinates e))).mul hφ).mul
    (Complex.continuous_conj.comp hψ)

theorem weightedProduct_leftInvariant (hU : IsUnipotent U) {φ ψ : Gₐ → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) ψ) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l)
      (weightedProduct p hK e β φ ψ) := by
  intro d hd g
  simp only [weightedProduct, IsIwasawaCompact.heightCoordinates,
    hK.height_leftInvariant_parabolic iU l hU d hd, hφ d hd, hψ d hd]

/-- Iwasawa coordinates compute the weighted pairing on the actual discrete parabolic
quotient using the compatible Haar measure. -/
theorem quotient_weightedProduct [IsIso (subgroupMultiplication l iU)]
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hμM : IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM) (hβ : Continuous β)
    {φ ψ : Gₐ → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) ψ) :
    let f := weightedProduct p hK e β φ ψ
    let W := inducedInnerProductIntegrand K p l e β φ ψ
    let mPair := (compactHaarProbability F G K hK.isCompact).prod ν
    (Integrable (fun z : LeftCosetSpace (principalParabolic p) => f z.out)
        (principalParabolicMeasure p) ↔ Integrable W mPair) ∧
    (Integrable W mPair → inducedInnerProduct K hK.isCompact p l μM e β φ ψ =
      ∫ z : LeftCosetSpace (principalParabolic p), f z.out ∂(principalParabolicMeasure p)) := by
  intro f W mPair
  obtain ⟨hI, hE⟩ := quotientIwasawa p iU l hK.isCompact μM hU hμM f
    (continuous_weightedProduct p hK e β hβ hφc hψc)
    (weightedProduct_leftInvariant p iU l hK e β hU.1.isUnipotent hφ hψ)
  have heq : (fun z : K × RationalQuotient F M =>
      (inverseModulus l z.2.out : ℂ) * f (mG z.2.out * z.1.val)) = W := by
    funext z
    have hy := hK.height_eq z.1.property (show mG z.2.out * z.1.val = _ from rfl)
    dsimp only [f, W, weightedProduct, inducedInnerProductIntegrand, IsIwasawaCompact.heightCoordinates]
    rw [hy, ofReal_inverseModulus]
    ring
  rw [heq] at hI hE
  exact ⟨hI, fun hi => (Langlands.Global.inducedInnerProduct_eq_integral_prod
    K hK.isCompact p l μM e β hi).trans hE.symm⟩

end Pairing

end InducedPairingCompactChange
end Langlands.Global.AdelicGroupPoints
