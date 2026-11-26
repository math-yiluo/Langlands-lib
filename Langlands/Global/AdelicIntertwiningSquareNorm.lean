import Langlands.Global.AdelicIntertwiningL2Estimate
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Global.AdelicIntertwiningLeviQuotient

/-! # The square norm of the normalized adelic intertwining integral -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions RestrictionSplitCentre
open InducedInnerProductIntegrable (parameterPower_zero continuous_parameterPower)

variable {F : Type} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P}
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q}
  (iU : U ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} {π' : Q ⟶ M'}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (hK' : IsIwasawaCompact q K)
  {φ : AdelicGroupPoints F G → ℂ}
  (hU : (SubgroupFunctor.range iU).IsNormal)
  (hi : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (he : IsSplitComponentEquivariant p l φ)

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
local notation "Γ" => intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
local notation "μV" => intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)
local notation "μK" => compactHaarProbability F G K hK.isCompact
local notation "μM" => canonicalMeasure F M
local notation "μM'" => canonicalMeasure F M'
local notation "Z" => K × CanonicalQuotient F M
local notation "Z'" => K × CanonicalQuotient F M'
local notation "wA" => innerAdelicPoint F G w
local notation "ml" => (fun m => map F P G p (map F M P l m))
local notation "nl" => normalizedLeviValue p l φ

include hU hi in
private theorem normalizedLeviValue_unipotent_mul (m : AdelicGroupPoints F M)
    {u : AdelicGroupPoints F G} (hu : u ∈ parabolicUnipotentImage F p iU)
    (g : AdelicGroupPoints F G) : nl m (u * g) = nl m g := by
  have hconj : ml m * u * (ml m)⁻¹ ∈ parabolicUnipotentImage F p iU :=
    conj_mem_adelicPoints_range p iU hU (map F M P l m) hu
  unfold normalizedLeviValue
  rw [show ml m * (u * g) = (ml m * u * (ml m)⁻¹) * (ml m * g) by group,
    hi _ (Subgroup.mem_sup_left hconj)]

include hU hi in
private theorem normalizedLeviValue_iwasawa (m b : AdelicGroupPoints F M)
    (u : AdelicGroupPoints F U) (g : AdelicGroupPoints F G) :
    nl m (map F U G (iU ≫ p) u * (ml b * g)) =
      parameterPower F P (halfModulusParameter F P) (map F M P l b) * nl (m * b) g := by
  rw [normalizedLeviValue_unipotent_mul iU hU hi m (show map F U G (iU ≫ p) u ∈
    parabolicUnipotentImage F p iU from ⟨u, rfl⟩)]
  have hcancel : parameterPower F P (halfModulusParameter F P) (map F M P l b) *
      parameterPower F P (-halfModulusParameter F P) (map F M P l b) = 1 := by
    rw [← InducedInnerProductIntegrable.parameterPower_add, add_neg_cancel, parameterPower_zero]
  unfold normalizedLeviValue
  rw [map_mul, InducedInnerProductIntegrable.parameterPower_mul, map_mul, mul_assoc (ml m),
    ← mul_assoc (parameterPower F P (halfModulusParameter F P) (map F M P l b))]
  rw [mul_left_comm (parameterPower F P (halfModulusParameter F P) (map F M P l b)),
    hcancel, mul_one]

private theorem heightPower_add (s t : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower (s + t) g = hK.heightPower s g * hK.heightPower t g := by
  simp only [IsIwasawaCompact.heightPower, map_add, LinearMap.add_apply, Complex.exp_add]

include hi he in
private theorem continuous_leadingRestriction (hφc : Continuous φ) :
    Continuous (fun z : Z => nl z.2.out z.1.val) := by
  refine LeftCosetSpace.continuous_out_of_invariant (canonicalRationalSubgroup F M)
    (fun (k : K) m => nl m k.val) ?_ ?_
  · have hMc : Continuous (fun z : K × AdelicGroupPoints F M => map F M P l z.2) :=
      (map F M P l).continuous.comp continuous_snd
    change Continuous (fun z : K × AdelicGroupPoints F M =>
      parameterPower F P (-halfModulusParameter F P) (map F M P l z.2) *
        φ (map F P G p (map F M P l z.2) * z.1.val))
    exact ((continuous_parameterPower _).comp hMc).mul
      (hφc.comp (((map F P G p).continuous.comp hMc).mul
        (continuous_subtype_val.comp continuous_fst)))
  · intro k
    exact normalizedLeviValue_invariant p l hi he k.val

include hi he in
private theorem continuous_transportedRestriction (e : M' ≅ M) (hφc : Continuous φ)
    {X : Type} [TopologicalSpace X] {g : X → AdelicGroupPoints F G} (hg : Continuous g) :
    Continuous (fun s : X × CanonicalQuotient F M' => nl (map F M' M e.hom s.2.out) (g s.1)) := by
  refine LeftCosetSpace.continuous_out_of_invariant (canonicalRationalSubgroup F M')
    (fun x m => nl (map F M' M e.hom m) (g x)) ?_ ?_
  · have hMc : Continuous (fun z : X × AdelicGroupPoints F M' => map F M P l (map F M' M e.hom z.2)) :=
      (map F M P l).continuous.comp ((map F M' M e.hom).continuous.comp continuous_snd)
    change Continuous (fun z : X × AdelicGroupPoints F M' =>
      parameterPower F P (-halfModulusParameter F P) (map F M P l (map F M' M e.hom z.2)) *
        φ (map F P G p (map F M P l (map F M' M e.hom z.2)) * g z.1))
    exact ((continuous_parameterPower _).comp hMc).mul
      (hφc.comp (((map F P G p).continuous.comp hMc).mul (hg.comp continuous_fst)))
  · intro x δ hδ m
    change nl (map F M' M e.hom (δ * m)) (g x) = nl (map F M' M e.hom m) (g x)
    rw [map_mul]
    exact normalizedLeviValue_invariant p l hi he (g x) _ (map_mem_canonicalRationalSubgroup e hδ) _

include hU hi he in
set_option maxHeartbeats 1200000 in
/-- The squared norm estimate for the regular operator, given the normalized change of
variables and a finite absolute integral of the scalar Iwasawa kernel. -/
theorem IsIwasawaCompact.intertwiningOperator_integrable_sq_norm
    (hw : IsWeylConjugation p l q l' w c) (hM : IsConnectedReductive M)
    (hM' : IsConnectedReductive M') (hφc : Continuous φ)
    (hUu : IsUnipotent U) (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left)
    (hVu : IsUnipotent V) (hV : (SubgroupFunctor.range iV).IsNormal)
    (hiU : IsClosedSubgroup (iU ≫ p)) (hπ' : l' ≫ π' = 𝟙 M')
    (hPK : ∀ g : AdelicGroupPoints F G, ∃ (u : AdelicGroupPoints F U)
      (b : AdelicGroupPoints F M) (k : K),
      g = map F U G (iU ≫ p) u * (ml b * (k : AdelicGroupPoints F G)))
    (hHaar : ∀ m, intertwiningLeviHaarFactor iU iV hw hU hV hiU hVu m *
      parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
      parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m))
    (hsource : Integrable (fun z : Z => ‖nl z.2.out z.1.val‖ ^ 2) (Measure.prod μK μM))
    (lam : ComplexCharacterParameter F P)
    (hκint : Integrable (fun v : LeftCosetSpace Γ =>
      hK.heightPower (lam + halfModulusParameter F P) (wA⁻¹ * (v.out : Vₐ).val)) μV) :
    Integrable (fun z : Z' => ‖normalizedLeviValue q l'
        (hK.intertwiningOperator hK' iU l iV c π' w φ lam) z.2.out z.1.val‖ ^ 2)
      (Measure.prod μK μM') := by
  let : IsIso c := hw.isIso
  let e := asIso c
  let : BorelSpace (CanonicalQuotient F M) := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let : BorelSpace (CanonicalQuotient F M') := canonicalQuotient_borelSpace F M' centralSplitTorusCharacter hM'
  let : PolishSpace Vₐ := (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA)
  let : IsLocallyFiniteMeasure μV := isLocallyFiniteMeasure_intertwiningMeasure p iU (iV ≫ q) w hVs hVc hVu
  let : SFinite μM := inferInstanceAs (SFinite (Measure.map _ (normOneRationalQuotientHaarMeasure F M)))
  let : SFinite μM' := inferInstanceAs (SFinite (Measure.map _ (normOneRationalQuotientHaarMeasure F M')))
  have huφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hi x (Subgroup.mem_sup_left hx) g
  let gV (v : Vₐ) := wA⁻¹ * v.val
  have hgVc : Continuous gV := continuous_const.mul continuous_subtype_val
  have hgVinv (δ : Vₐ) (hδ : δ ∈ Γ) (v : Vₐ) :
      ∃ u : AdelicGroupPoints F U, gV (δ * v) = map F U G (iU ≫ p) u * gV v := by
    obtain ⟨u, hu⟩ := ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA δ).mp hδ).2
    refine ⟨u, ?_⟩
    change wA⁻¹ * (δ.val * v.val) = map F U G (iU ≫ p) u * (wA⁻¹ * v.val)
    change map F U G (iU ≫ p) u = wA⁻¹ * δ.val * wA at hu
    rw [hu]
    group
  have heightInvariant (s : ComplexCharacterParameter F P) (δ : Vₐ) (hδ : δ ∈ Γ) (v : Vₐ) :
      hK.heightPower s (gV (δ * v)) = hK.heightPower s (gV v) := by
    obtain ⟨u, hu⟩ := hgVinv δ hδ v
    rw [hu, hK.heightPower_unipotent_mul hUu]
  let κ (v : LeftCosetSpace Γ) := hK.heightPower (lam + halfModulusParameter F P) (gV v.out)
  have hκ : Measurable κ := LeftCosetSpace.measurable_out_of_invariant Γ
    ((hK.continuous_heightPower _).comp hgVc).measurable (heightInvariant _)
  let sourceValue (z : Z) := nl z.2.out z.1.val
  have hsourcec : Continuous sourceValue := continuous_leadingRestriction iU hi he hφc
  let sectionValue (v : Vₐ) (z : Z') :=
    hK.heightPower (-halfModulusParameter F P) (gV v) *
      nl (map F M' M c z.2.out) (gV v * z.1.val)
  have hsectionc : Continuous (fun vz : Vₐ × Z' => sectionValue vz.1 vz.2) := by
    have hg : Continuous (fun vk : Vₐ × K => gV vk.1 * vk.2.val) := by fun_prop
    have hc := continuous_transportedRestriction iU hi he e hφc hg
    have hassoc : Continuous (fun vz : Vₐ × Z' => ((vz.1, vz.2.1), vz.2.2)) := by fun_prop
    change Continuous (fun vz : Vₐ × Z' =>
      hK.heightPower (-halfModulusParameter F P) (gV vz.1) *
        nl (map F M' M e.hom vz.2.2.out) (gV vz.1 * vz.2.1.val))
    apply Continuous.mul
    · exact (hK.continuous_heightPower _).comp (hgVc.comp continuous_fst)
    · simpa only [Function.comp_def] using (hc.comp hassoc)
  let f (v : LeftCosetSpace Γ) (z : Z') := sectionValue v.out z
  have hf : Measurable (fun vz : LeftCosetSpace Γ × Z' => f vz.1 vz.2) := by
    have h : Continuous (fun zv : Z' × LeftCosetSpace Γ => f zv.2 zv.1) := by
      refine LeftCosetSpace.continuous_out_of_invariant Γ (fun z v => sectionValue v z) ?_ ?_
      · simpa only [Function.comp_def, Prod.swap] using (hsectionc.comp continuous_swap)
      · intro z δ hδ v
        obtain ⟨u, hu⟩ := hgVinv δ hδ v
        unfold sectionValue
        rw [heightInvariant _ δ hδ v, hu, mul_assoc, normalizedLeviValue_unipotent_mul iU hU hi]
        exact ⟨u, rfl⟩
    have hSwap : Continuous (fun vz : LeftCosetSpace Γ × Z' => f vz.1 vz.2) := by
      simpa only [Function.comp_def, Prod.swap] using (h.comp continuous_swap)
    exact hSwap.measurable
  obtain ⟨s, _, hs⟩ := map_canonicalMeasure (F := F) e
  let B := ∫⁻ z, ‖sourceValue z‖ₑ ^ 2 ∂(Measure.prod μK μM)
  have hB : B ≠ ∞ := by
    have h := hasFiniteIntegral_iff_enorm.mp hsource.hasFiniteIntegral
    have hsq (a : ℂ) : ‖(‖a‖ ^ 2 : ℝ)‖ₑ = ‖a‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg ‖a‖), ENNReal.ofReal_pow (norm_nonneg a), ofReal_norm]
    simpa only [B, sourceValue, hsq, lt_top_iff_ne_top] using h
  have hfbound (v : LeftCosetSpace Γ) : (∫⁻ z, ‖f v z‖ₑ ^ 2 ∂(Measure.prod μK μM')) ≤ (s : ℝ≥0∞) * B := by
    obtain ⟨u, b, k, hdecomp⟩ := hPK (gV v.out)
    let r := LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F M) b
    let t : Z' → Z := fun z => (k * z.1, r (canonicalQuotientMap e z.2))
    have hr : MeasurePreserving r μM μM := canonicalMeasure_rightInvariant F M centralSplitTorusCharacter hM b
    have hk := measurePreserving_mul_left μK k
    have ht : Measurable t := (hk.measurable.comp measurable_fst).prodMk
      ((hr.measurable.comp (measurable_canonicalQuotientMap e)).comp measurable_snd)
    have hmap : Measure.map t (Measure.prod μK μM') = (s : ℝ≥0∞) • Measure.prod μK μM := by
      change Measure.map (Prod.map (fun x => k * x) (r ∘ canonicalQuotientMap e)) _ = _
      rw [← Measure.map_prod_map _ _ hk.measurable (hr.measurable.comp (measurable_canonicalQuotientMap e)),
        hk.map_eq, ← Measure.map_map hr.measurable (measurable_canonicalQuotientMap e), hs,
        Measure.map_smul (s : ℝ≥0∞) hr.measurable.aemeasurable, hr.map_eq, Measure.prod_smul_right]
    have heval (z : Z') : f v z = sourceValue (t z) := by
      have hh : hK.heightPower (-halfModulusParameter F P) (gV v.out) =
          parameterPower F P (-halfModulusParameter F P) (map F M P l b) := by
        have hdecomp' := hdecomp
        change gV v.out = map F U G (iU ≫ p) u *
          (map F P G p (map F M P l b) * k.val) at hdecomp'
        rw [hdecomp', map_comp_apply_of_hom (p := p) iU, ← mul_assoc, ← map_mul]
        unfold IsIwasawaCompact.heightPower parameterPower
        rw [hK.height_eq_levi hUu iU l u b k.property, characterLog_map]
      have hc (z : Z') : (t z).2 = LeftCosetSpace.mk (canonicalRationalSubgroup F M)
          (map F M' M c z.2.out * b) := by
        dsimp only [t, r]
        have hz : LeftCosetSpace.mk (canonicalRationalSubgroup F M') z.2.out = z.2 := Quotient.out_eq _
        calc
          _ = LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F M) b
              (canonicalQuotientMap e (LeftCosetSpace.mk (canonicalRationalSubgroup F M') z.2.out)) :=
            congrArg (fun x => LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F M) b
              (canonicalQuotientMap e x)) hz.symm
          _ = _ := rfl
      have hcancel : parameterPower F P (-halfModulusParameter F P) (map F M P l b) *
          parameterPower F P (halfModulusParameter F P) (map F M P l b) = 1 := by
        rw [← InducedInnerProductIntegrable.parameterPower_add, neg_add_cancel, parameterPower_zero]
      change hK.heightPower (-halfModulusParameter F P) (gV v.out) * nl (map F M' M c z.2.out)
        (gV v.out * z.1.val) = nl (t z).2.out (k * z.1 : K).val
      rw [hh, hdecomp, mul_assoc, mul_assoc, normalizedLeviValue_iwasawa iU hU hi,
        ← mul_assoc, hcancel, one_mul, hc]
      exact (LeftCosetSpace.out_mk_of_invariant _ (fun m => nl m (k * z.1 : K).val)
        (normalizedLeviValue_invariant p l hi he _) _).symm
    apply le_of_eq
    simp_rw [heval]
    rw [← lintegral_map (hsourcec.measurable.enorm.pow_const 2) ht, hmap, lintegral_smul_measure]
    rfl
  have hI := integrable_sq_norm_kernelIntegral hκ hκint hf (ENNReal.mul_ne_top ENNReal.coe_ne_top hB) hfbound
  refine hI.congr (Filter.Eventually.of_forall fun z => congrArg (fun x : ℂ => ‖x‖ ^ 2) ?_)
  have hheight : hK'.heightPower (-weylParameter l c π' lam) z.1.val = 1 := by
    simp only [IsIwasawaCompact.heightPower, hK'.height_of_mem z.1.property, map_zero, Complex.exp_zero]
  have hnorm := hK.intertwiningOperator_normalized_levi iU iV hw hU hV hiU hVu hK' hπ'
    hVs hVc hUu hφc huφ z.2.out lam z.1.val (hHaar z.2.out)
  rw [hheight, one_mul] at hnorm
  rw [normalizedLeviValue, hnorm]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  change hK.heightPower (lam + halfModulusParameter F P) (gV v.out) *
      (hK.heightPower (-halfModulusParameter F P) (gV v.out) *
        nl (map F M' M c z.2.out) (gV v.out * z.1.val)) =
    nl (map F M' M c z.2.out) (gV v.out * z.1.val) * hK.heightPower lam (gV v.out * z.1.val)
  have hcancel : hK.heightPower (halfModulusParameter F P) (gV v.out) *
      hK.heightPower (-halfModulusParameter F P) (gV v.out) = 1 := by
    rw [← heightPower_add, add_neg_cancel]
    simp [IsIwasawaCompact.heightPower]
  let value := nl (map F M' M c z.2.out) (gV v.out * z.1.val)
  have hright : hK.heightPower lam (gV v.out * z.1.val) = hK.heightPower lam (gV v.out) := by
    unfold IsIwasawaCompact.heightPower
    rw [hK.height_mul_right _ z.1.property]
  rw [heightPower_add, hright]
  calc
    _ = value * hK.heightPower lam (gV v.out) *
        (hK.heightPower (halfModulusParameter F P) (gV v.out) *
          hK.heightPower (-halfModulusParameter F P) (gV v.out)) := by dsimp only [value]; ring
    _ = _ := by rw [hcancel, mul_one]

end Langlands.Global.AdelicGroupPoints
