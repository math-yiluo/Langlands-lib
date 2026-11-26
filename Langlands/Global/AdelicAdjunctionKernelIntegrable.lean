import Langlands.Global.AdelicAdjunctionNormalizedKernel
import Langlands.Global.AdelicIntertwiningSquareNorm

/-! # Absolute integrability of the normalized adjunction kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

private theorem integral_enorm_sq_lt_top {X : Type} [MeasurableSpace X] {μ : Measure X}
    (f : X → ℂ) (hf : Integrable (fun x => ‖f x‖ ^ 2) μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞ := by
  have h := hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral
  have hsq (a : ℂ) : ‖(‖a‖ ^ 2 : ℝ)‖ₑ = ‖a‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg ‖a‖), ENNReal.ofReal_pow (norm_nonneg a), ofReal_norm]
  simpa only [hsq] using h

private theorem enorm_prod_conj_le_sq (a b : ℂ) : ‖a * (starRingEnd ℂ) b‖ₑ ≤ ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 := by
  simp only [← ofReal_norm, norm_mul, Complex.norm_conj, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A uniform squared-norm bound in the second variable suffices to integrate the
pairing kernel against an integrable scalar kernel and a fixed square-integrable vector. -/
private theorem integrable_kernelPair {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (κ : X → ℂ) (hκ : Measurable κ) (hκi : Integrable κ μ)
    (f : X × Y → ℂ) (hf : Measurable f) (g : Y → ℂ) (hg : Measurable g)
    (B : ℝ≥0∞) (hB : B < ∞) (hfB : ∀ x, (∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν) ≤ B)
    (hgi : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    Integrable (fun z => κ z.1 * f z * (starRingEnd ℂ) (g z.2)) (μ.prod ν) := by
  have hF : Measurable (fun z => κ z.1 * f z * (starRingEnd ℂ) (g z.2)) :=
    ((hκ.comp measurable_fst).mul hf).mul (continuous_star.measurable.comp (hg.comp measurable_snd))
  refine ⟨hF.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  let D := ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν
  have hD : D < ∞ := integral_enorm_sq_lt_top g hgi
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ x, ‖κ x‖ₑ * (B + D) ∂μ := by
      apply lintegral_mono
      intro x
      have hx : Measurable (fun y => ‖f (x, y)‖ₑ ^ 2) := hf.enorm.pow_const 2 |>.comp measurable_prodMk_left
      have hy : Measurable (fun y => ‖g y‖ₑ ^ 2) := hg.enorm.pow_const 2
      calc
        _ ≤ ∫⁻ y, ‖κ x‖ₑ * (‖f (x, y)‖ₑ ^ 2 + ‖g y‖ₑ ^ 2) ∂ν := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [mul_assoc, enorm_mul]
          gcongr
          exact enorm_prod_conj_le_sq _ _
        _ = ‖κ x‖ₑ * ((∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν) + D) := by
          have hsum : Measurable (fun y => ‖f (x, y)‖ₑ ^ 2 + ‖g y‖ₑ ^ 2) := hx.add hy
          rw [lintegral_const_mul _ hsum, lintegral_add_left hx]
        _ ≤ _ := by dsimp only; gcongr; exact hfB x
    _ < ∞ := by
      rw [lintegral_mul_const _ hκ.enorm]
      exact ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp hκi.hasFiniteIntegral)
        (ENNReal.add_lt_top.mpr ⟨hB, hD⟩)

end Langlands.Global

namespace Langlands.Global.AdelicGroupPoints

open scoped CategoryTheory.MonObj

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open InducedInnerProductIntegrable ParabolicIwasawaMeasure RestrictionSplitCentre LeftCosetSpace

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] [IsIso (subgroupMultiplication l iU)]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left] [IsIso (subgroupMultiplication l' iV)]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (c : M' ⟶ M) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  {φ ψ : AdelicGroupPoints F G → ℂ} (lam : ComplexCharacterParameter F P)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l') ψ)
  (heφ : IsSplitComponentEquivariant p l φ) (heψ : IsSplitComponentEquivariant q l' ψ)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "wA" => (innerAdelicPoint F G w)
local notation "Vₐ" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
local notation "Uₐ" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)))
local notation "Δ" => (intertwiningRationalSubgroup F p iU (iV ≫ q) wA)
local notation "Xᵥ" => (LeftCosetSpace Δ)
local notation "μV" => (intertwiningMeasure F p iU (iV ≫ q) wA)
local notation "mP" => (map F M P l)
local notation "gP" => (fun m => map F P G p (mP m))
local notation "xV" => (fun (v : Vₐ) => wA⁻¹ * Subtype.val v)
local notation "μK" => (compactHaarProbability F G K (IsIwasawaCompact.isCompact hK))
local notation "Z" => (K × CanonicalQuotient F M)
local notation "Z'" => (K × CanonicalQuotient F M')
local notation "μZ" => (Measure.prod μK (canonicalMeasure F M))
local notation "μZ'" => (Measure.prod μK (canonicalMeasure F M'))

include hU hφ in
private theorem normalizedLeviValue_left_radical (m : AdelicGroupPoints F M)
    {u : Gₐ} (hu : u ∈ parabolicUnipotentImage F p iU) (g : Gₐ) :
    normalizedLeviValue p l φ m (u * g) = normalizedLeviValue p l φ m g := by
  have hconj : gP m * u * (gP m)⁻¹ ∈ parabolicUnipotentImage F p iU :=
    conj_mem_adelicPoints_range p iU hU.1.isNormal (mP m) hu
  unfold normalizedLeviValue
  rw [show gP m * (u * g) = (gP m * u * (gP m)⁻¹) * (gP m * g) by dsimp only; group,
    hφ _ (Subgroup.mem_sup_left hconj)]

include hU hφ in
private theorem normalizedLeviValue_radicalLevi (m b : AdelicGroupPoints F M)
    (u : Uₐ) (g : Gₐ) :
    normalizedLeviValue p l φ m (u.val * (gP b * g)) =
      parameterPower F P (halfModulusParameter F P) (mP b) * normalizedLeviValue p l φ (m * b) g := by
  rw [normalizedLeviValue_left_radical iU l hU hφ m u.property]
  have hcancel : parameterPower F P (halfModulusParameter F P) (mP b) *
      parameterPower F P (-halfModulusParameter F P) (mP b) = 1 := by
    rw [← parameterPower_add, add_neg_cancel, parameterPower_zero]
  unfold normalizedLeviValue
  rw [map_mul, parameterPower_mul, map_mul, mul_assoc (gP m),
    ← mul_assoc (parameterPower F P (halfModulusParameter F P) (mP b))]
  rw [mul_left_comm (parameterPower F P (halfModulusParameter F P) (mP b)), hcancel, mul_one]

private theorem translate_xV (d : Δ) (v : Vₐ) :
    xV (d.val * v) = (wA⁻¹ * d.val.val * wA) * xV v := by
  dsimp only [Subgroup.coe_mul]
  group

include hU l in
/-- The source height shift of the moved radical coordinate is measurable. -/
theorem measurable_adjunctionHeightShift {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Measurable (fun v : Xᵥ => hK.heightCoordinates e (xV (v.out : Vₐ))) := by
  refine measurable_out_of_invariant Δ ((hK.continuous_heightCoordinates e).comp
    (continuous_const.mul continuous_subtype_val)).measurable ?_
  intro d hd v
  change hK.heightCoordinates e (xV (d * v)) = hK.heightCoordinates e (xV v)
  rw [translate_xV iU iV w (⟨d, hd⟩ : Δ) v]
  have hdu := ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA d).1 hd).2
  unfold IsIwasawaCompact.heightCoordinates
  rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ (Subgroup.mem_sup_left hdu)]

private def adjunctionSourceFactor (v : Vₐ) (k : K) (m : AdelicGroupPoints F M') : ℂ := hK.heightPower (-halfModulusParameter F P) (xV v) *
    normalizedLeviValue p l φ (map F M' M c m) (xV v * k.val)

include hU hφ heφ in
set_option maxHeartbeats 2500000 in
private theorem measurable_adjunctionSourceFactor (hw : IsWeylConjugation p l q l' w c)
    (hM' : IsConnectedReductive M') (hφc : Continuous φ) :
    Measurable (fun z : Xᵥ × Z' => adjunctionSourceFactor (q := q) l iV hK c w (φ := φ)
      z.1.out z.2.1 z.2.2.out) := by
  let : IsIso c := hw.isIso
  let cIso := asIso c
  let : BorelSpace (CanonicalQuotient F M') := canonicalQuotient_borelSpace F M' centralSplitTorusCharacter hM'
  let hVclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : PolishSpace Vₐ := hVclosed.polishSpace
  let hΔ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let f := adjunctionSourceFactor (q := q) l iV hK c w (φ := φ)
  change Measurable (fun z : Xᵥ × Z' => f z.1.out z.2.1 z.2.2.out)
  have hrad (d : Δ) : wA⁻¹ * d.val.val * wA ∈ parabolicUnipotentImage F p iU :=
    ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA d.val).1 d.property).2
  have hpow (s : ComplexCharacterParameter F P) (d : Δ) (v : Vₐ) :
      hK.heightPower s (xV (d.val * v)) = hK.heightPower s (xV v) := by
    rw [translate_xV iU iV w d v]
    unfold IsIwasawaCompact.heightPower
    rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ (Subgroup.mem_sup_left (hrad d))]
  let f₀ : (Vₐ × K) × AdelicGroupPoints F M' → ℂ := fun z => f z.1.1 z.1.2 z.2
  have hg : Continuous (fun z : Vₐ × K => xV z.1 * z.2.val) := by fun_prop
  have hf₀ : Continuous f₀ := by
    apply Continuous.mul
    · exact (hK.continuous_heightPower _).comp ((continuous_const.mul continuous_subtype_val).comp
        (continuous_fst.comp continuous_fst))
    · let t : (Vₐ × K) × AdelicGroupPoints F M' → AdelicGroupPoints F M × Gₐ :=
        fun z => (map F M' M c z.2, xV z.1.1 * z.1.2.val)
      have ht : Continuous t := ((map F M' M c).continuous.comp continuous_snd).prodMk
        (hg.comp continuous_fst)
      change Continuous ((fun z : AdelicGroupPoints F M × Gₐ => normalizedLeviValue p l φ z.1 z.2) ∘ t)
      exact (continuous_normalizedLeviValue p l hφc).comp ht
  have hf1 : Continuous (fun z : (Vₐ × K) × CanonicalQuotient F M' => f z.1.1 z.1.2 z.2.out) :=
    continuous_out_of_invariant (X := Vₐ × K) (E := ℂ) (canonicalRationalSubgroup F M')
      (fun z m => f z.1 z.2 m) hf₀ (by
      intro z d hd m
      dsimp only [f, adjunctionSourceFactor]
      have hd' : map F M' M c d ∈ canonicalRationalSubgroup F M :=
        map_mem_canonicalRationalSubgroup cIso hd
      rw [map_mul, normalizedLeviValue_invariant p l hφ heφ _ _ hd'])
  let s : Z' × Vₐ → (Vₐ × K) × CanonicalQuotient F M' := fun x => ((x.2, x.1.1), x.1.2)
  have hs : Continuous s := by dsimp only [s]; fun_prop
  have hf2 : Measurable (fun z : Z' × Xᵥ => f z.2.out z.1.1 z.1.2.out) := by
    have hm : Measurable (fun z : Z' × Vₐ => f z.2 z.1.1 z.1.2.out) := (hf1.comp hs).measurable
    refine measurable_out_of_invariant_prod (X := Z') (Γ := Δ) hΔ (fun z v => f v z.1 z.2.out) hm ?_
    intro z d hd v
    dsimp only [f, adjunctionSourceFactor]
    have hdv : wA⁻¹ * (d * v).val = (wA⁻¹ * d.val * wA) * xV v :=
      translate_xV iU iV w (⟨d, hd⟩ : Δ) v
    rw [hpow _ ⟨d, hd⟩ v, hdv, mul_assoc,
      normalizedLeviValue_left_radical iU l hU hφ _ (hrad ⟨d, hd⟩)]
  change Measurable ((fun z : Z' × Xᵥ => f z.2.out z.1.1 z.1.2.out) ∘ Prod.swap)
  exact hf2.comp measurable_swap

include hφ heφ in
private theorem continuous_normalizedRestriction (hφc : Continuous φ) :
    Continuous (fun z : Z => normalizedLeviValue p l φ z.2.out z.1.val) := by
  refine continuous_out_of_invariant (canonicalRationalSubgroup F M)
    (fun (k : K) m => normalizedLeviValue p l φ m k.val) ?_ ?_
  · have hMc : Continuous (fun z : K × AdelicGroupPoints F M => map F M P l z.2) :=
      (map F M P l).continuous.comp continuous_snd
    change Continuous (fun z : K × AdelicGroupPoints F M =>
      parameterPower F P (-halfModulusParameter F P) (mP z.2) * φ (gP z.2 * z.1.val))
    exact ((continuous_parameterPower _).comp hMc).mul
      (hφc.comp (((map F P G p).continuous.comp hMc).mul
        (continuous_subtype_val.comp continuous_fst)))
  · intro k
    exact normalizedLeviValue_invariant p l hφ heφ k.val

include hU hφ heφ in
set_option maxHeartbeats 1000000 in
private theorem adjunctionSourceFactor_bound (hw : IsWeylConjugation p l q l' w c)
    (hM : IsConnectedReductive M) (hφc : Continuous φ)
    (hφsq : Integrable (fun z : Z => ‖normalizedLeviValue p l φ z.2.out z.1.val‖ ^ 2) μZ) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ v : Xᵥ, (∫⁻ z : Z',
      ‖adjunctionSourceFactor (q := q) l iV hK c w (φ := φ) v.out z.1 z.2.out‖ₑ ^ 2 ∂μZ') ≤ B := by
  let : IsIso c := hw.isIso
  let cIso := asIso c
  let : BorelSpace (CanonicalQuotient F M) := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let : SFinite (canonicalMeasure F M) := inferInstanceAs (SFinite (Measure.map _ (normOneRationalQuotientHaarMeasure F M)))
  let : SFinite (canonicalMeasure F M') := inferInstanceAs (SFinite (Measure.map _ (normOneRationalQuotientHaarMeasure F M')))
  let f := adjunctionSourceFactor (q := q) l iV hK c w (φ := φ)
  let fv (z : Xᵥ × Z') : ℂ := f z.1.out z.2.1 z.2.2.out
  let φv (z : Z) : ℂ := normalizedLeviValue p l φ z.2.out z.1.val
  have hφc' : Continuous φv := continuous_normalizedRestriction iU l hφ heφ hφc
  obtain ⟨s, _, hs⟩ := map_canonicalMeasure (F := F) cIso
  let B := (s : ℝ≥0∞) * ∫⁻ z, ‖φv z‖ₑ ^ 2 ∂μZ
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (integral_enorm_sq_lt_top φv hφsq)
  refine ⟨B, hB, fun v => ?_⟩
  · obtain ⟨x, k, hk, hx⟩ := hK.exists_eq (xV (v.out : Vₐ))
    obtain ⟨⟨u, b⟩, rfl⟩ := (coordinates p iU l hU).surjective x
    let k₀ : K := ⟨k, hk⟩
    have hgv : xV (v.out : Vₐ) = u.val * (gP b * k₀.val) := by
      rw [← hx]
      exact (congrArg (fun y : Gₐ => y * k) (map_coordinates p iU l hU (u, b))).trans
        (mul_assoc u.val _ _)
    let t : Z' → Z := fun z => (k₀ * z.1,
      rightTranslate (canonicalRationalSubgroup F M) b (canonicalQuotientMap cIso z.2))
    have hr : MeasurePreserving (rightTranslate (canonicalRationalSubgroup F M) b)
        (canonicalMeasure F M) (canonicalMeasure F M) :=
      canonicalMeasure_rightInvariant F M centralSplitTorusCharacter hM b
    have hk₀ := measurePreserving_mul_left μK k₀
    have hq₀ := measurable_canonicalQuotientMap (F := F) cIso
    have ht : Measurable t := (hk₀.measurable.comp measurable_fst).prodMk
      ((hr.measurable.comp hq₀).comp measurable_snd)
    have htmap : Measure.map t μZ' = (s : ℝ≥0∞) • μZ := by
      change Measure.map (Prod.map (fun k => k₀ * k)
        (rightTranslate (canonicalRationalSubgroup F M) b ∘ canonicalQuotientMap cIso)) _ = _
      rw [← Measure.map_prod_map _ _ hk₀.measurable (hr.measurable.comp hq₀), hk₀.map_eq,
        ← Measure.map_map hr.measurable hq₀, hs, Measure.map_smul _ hr.measurable.aemeasurable,
        hr.map_eq, Measure.prod_smul_right]
    have hval (z : Z') : fv (v, z) = φv (t z) := by
      have hh : hK.heightPower (-halfModulusParameter F P) (xV (v.out : Vₐ)) =
          parameterPower F P (-halfModulusParameter F P) (mP b) := by
        rw [hgv]
        have hu : u.val ∈ parabolicQuotientSubgroup F p iU l := Subgroup.mem_sup_left u.property
        unfold IsIwasawaCompact.heightPower parameterPower
        rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ hu, hK.height_eq k₀.property rfl]
      have hcancel : parameterPower F P (-halfModulusParameter F P) (mP b) *
          parameterPower F P (halfModulusParameter F P) (mP b) = 1 := by
        rw [← parameterPower_add, neg_add_cancel, parameterPower_zero]
      have hc (z : Z') : (t z).2 = mk (canonicalRationalSubgroup F M) (map F M' M c z.2.out * b) := by
        let m := fun q => rightTranslate (canonicalRationalSubgroup F M) b (canonicalQuotientMap cIso q)
        exact congrArg m (Quotient.out_eq z.2).symm
      change hK.heightPower (-halfModulusParameter F P) (xV (v.out : Vₐ)) *
        normalizedLeviValue p l φ (map F M' M c z.2.out) (xV (v.out : Vₐ) * z.1.val) =
        normalizedLeviValue p l φ (t z).2.out (k₀ * z.1 : K).val
      rw [hh, hgv, mul_assoc u.val, mul_assoc (gP b), normalizedLeviValue_radicalLevi iU l hU hφ,
        ← mul_assoc, hcancel, one_mul, hc]
      symm
      exact out_mk_of_invariant _ (fun m => normalizedLeviValue p l φ m (k₀ * z.1 : K).val)
        (normalizedLeviValue_invariant p l hφ heφ _) _
    change (∫⁻ z, ‖fv (v, z)‖ₑ ^ 2 ∂μZ') ≤ B
    apply le_of_eq
    simp_rw [hval]
    rw [← lintegral_map (hφc'.measurable.enorm.pow_const 2) ht, htmap, lintegral_smul_measure]
    rfl

include hU hφ hψ heφ heψ in
set_option maxHeartbeats 1000000 in
/-- The normalized product is absolutely integrable over the radical quotient and the
compact times canonical target Levi quotient. -/
theorem integrable_normalizedAdjunctionKernel (hw : IsWeylConjugation p l q l' w c)
    (hM : IsConnectedReductive M) (hM' : IsConnectedReductive M') (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφsq : Integrable (fun z : Z => ‖normalizedLeviValue p l φ z.2.out z.1.val‖ ^ 2) μZ)
    (hψsq : Integrable (fun z : Z' => ‖normalizedLeviValue q l' ψ z.2.out z.1.val‖ ^ 2) μZ')
    (hκi : Integrable (fun v : Xᵥ => hK.heightPower (lam + halfModulusParameter F P) (xV (v.out : Vₐ))) μV) :
    let J : Xᵥ × Z' → ℂ := fun z => normalizedAdjunctionKernel l iV l' hK w φ ψ lam c
      z.1.out z.2.2.out z.2.1
    Measurable J ∧ Integrable J (Measure.prod μV μZ') := by
  let : BorelSpace (CanonicalQuotient F M') := canonicalQuotient_borelSpace F M' centralSplitTorusCharacter hM'
  let hVclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : PolishSpace Vₐ := hVclosed.polishSpace
  let hΔ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let : BorelSpace Xᵥ := discreteQuotientBorelSpace Δ hΔ
  let : SFinite (canonicalMeasure F M') := inferInstanceAs (SFinite (Measure.map _ (normOneRationalQuotientHaarMeasure F M')))
  let κ (v : Xᵥ) : ℂ := hK.heightPower (lam + halfModulusParameter F P) (xV (v.out : Vₐ))
  let f := adjunctionSourceFactor (q := q) l iV hK c w (φ := φ)
  let fv (z : Xᵥ × Z') : ℂ := f z.1.out z.2.1 z.2.2.out
  let ψv (z : Z') : ℂ := normalizedLeviValue q l' ψ z.2.out z.1.val
  have hrad (d : Δ) : wA⁻¹ * d.val.val * wA ∈ parabolicUnipotentImage F p iU :=
    ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA d.val).1 d.property).2
  have hpow (s : ComplexCharacterParameter F P) (d : Δ) (v : Vₐ) :
      hK.heightPower s (xV (d.val * v)) = hK.heightPower s (xV v) := by
    rw [translate_xV iU iV w d v]
    unfold IsIwasawaCompact.heightPower
    rw [hK.height_leftInvariant_parabolic iU l hU.1.isUnipotent _ (Subgroup.mem_sup_left (hrad d))]
  have hκ : Measurable κ := measurable_out_of_invariant Δ
    ((hK.continuous_heightPower _).comp (continuous_const.mul continuous_subtype_val)).measurable
    (fun d hd v => hpow _ ⟨d, hd⟩ v)
  have hfv : Measurable fv := measurable_adjunctionSourceFactor iU l iV l' hK c w hU hφ heφ hw hM' hφc
  have hψc' : Continuous ψv := continuous_normalizedRestriction iV l' hψ heψ hψc
  obtain ⟨B, hB, hfB⟩ := adjunctionSourceFactor_bound iU l iV l' hK c w hU hφ heφ hw hM hφc hφsq
  have hJ (z : Xᵥ × Z') : κ z.1 * fv z * (starRingEnd ℂ) (ψv z.2) =
      normalizedAdjunctionKernel l iV l' hK w φ ψ lam c z.1.out z.2.2.out z.2.1 := by
    have hAdd : hK.heightPower (lam + halfModulusParameter F P) (xV (z.1.out : Vₐ)) *
        hK.heightPower (-halfModulusParameter F P) (xV (z.1.out : Vₐ)) =
          hK.heightPower lam (xV (z.1.out : Vₐ)) := by
      simp only [IsIwasawaCompact.heightPower, ← Complex.exp_add, ← LinearMap.add_apply, ← map_add,
        add_neg_cancel_right]
    unfold normalizedAdjunctionKernel
    dsimp only [κ, fv, f, adjunctionSourceFactor, ψv]
    rw [← mul_assoc, hAdd]
  have hm : Measurable (fun z : Xᵥ × Z' => κ z.1 * fv z * (starRingEnd ℂ) (ψv z.2)) :=
    ((hκ.comp measurable_fst).mul hfv).mul (continuous_star.measurable.comp (hψc'.measurable.comp measurable_snd))
  refine ⟨(funext hJ) ▸ hm, ?_⟩
  exact (integrable_kernelPair μV μZ' κ hκ hκi fv hfv ψv hψc'.measurable B hB hfB hψsq).congr
    (Filter.Eventually.of_forall hJ)

end Langlands.Global.AdelicGroupPoints
