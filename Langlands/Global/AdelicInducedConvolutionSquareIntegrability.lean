import Langlands.Global.AdelicInducedConvolutionCompact
import Langlands.Global.AdelicInducedConvolutionCovariance
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Square integrability of adelic induced convolution -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Global.InducedInnerProductIntegrable
open Langlands.Global.InducedInnerProductSesquilinear
  (normWeight normWeight_splitComponent_mul normWeight_rational_mul)

/-- Cauchy–Schwarz and Fubini on a product with a finite integration measure. -/
private theorem integrable_sq_norm_integral_of_prod {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (mx : Measure X) (my : Measure Y) [SFinite mx] [IsFiniteMeasure my]
    {f : X × Y → ℂ} (hf : AEStronglyMeasurable f (mx.prod my))
    (hsq : Integrable (fun z => ‖f z‖ ^ 2) (mx.prod my)) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂my‖ ^ 2) mx := by
  have hmajorant := hsq.integral_prod_left.const_mul (my.real univ)
  refine hmajorant.mono' (hf.integral_prod_right'.norm.pow 2) ?_
  filter_upwards [hf.prodMk_left, hsq.prod_right_ae] with x hxm hxi
  let g (y : Y) := f (x, y)
  have hg : MemLp g 2 my := (memLp_two_iff_integrable_sq_norm hxm).mpr hxi
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) my := by simpa using hg
  have h₁ : MemLp (fun _ : Y => (1 : ℂ)) (ENNReal.ofReal (2 : ℝ)) my := memLp_const _
  have hhol := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hg' h₁
  have hnn : 0 ≤ ∫ y, ‖g y‖ ^ 2 ∂my := integral_nonneg fun _ => sq_nonneg _
  have hbound : ‖∫ y, g y ∂my‖ ≤
      Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂my) * Real.sqrt (my.real univ) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_one, mul_one, Real.rpow_two, one_pow,
      integral_const, smul_eq_mul, ← Real.sqrt_eq_rpow] using hhol
  have hsq' := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [mul_pow, Real.sq_sqrt hnn, Real.sq_sqrt measureReal_nonneg, mul_comm] at hsq'
  change ‖‖∫ y, g y ∂my‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq'

section Normalization

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left]
  [LocallyOfFiniteType P.X.hom] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) (iU : U ⟶ P)

local notation "H" => AdelicGroupPoints F G
local notation "Qlevi" => RestrictionSplitCentre.CanonicalQuotient F M
local notation "Γ" => RestrictionSplitCentre.canonicalRationalSubgroup F M

private def normalizedValue (v : H → ℂ) (g : H) (m : Qlevi) : ℂ :=
  parameterPower F P (-halfModulusParameter F P) (map F M P l m.out) *
    v (map F P G p (map F M P l m.out) * g)

omit [IsAffine G.X.left] in
private theorem norm_sq_normalizedValue (v : H → ℂ) (g : H) (m : Qlevi) :
    ‖normalizedValue p l v g m‖ ^ 2 = normWeight p l v g m.out := by
  have hpar : -halfModulusParameter F P + -halfModulusParameter F P = -modulusParameter F P := by
    have h := neg_modulus_add_half_add_half (F := F) (P := P)
    calc
      _ = (-modulusParameter F P + halfModulusParameter F P + halfModulusParameter F P) +
          (-halfModulusParameter F P + -halfModulusParameter F P) := by rw [h, zero_add]
      _ = _ := by abel
  rw [normalizedValue, normWeight, norm_mul, mul_pow, sq, ← norm_mul, ← parameterPower_add, hpar]

private theorem continuous_normalizedValue [LocallyOfFiniteType G.X.hom]
    {v : H → ℂ} (hc : Continuous v)
    (hi : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) v)
    (he : IsSplitComponentEquivariant p l v) :
    Continuous (fun z : H × Qlevi => normalizedValue p l v z.1 z.2) := by
  let f (g : H) (m : AdelicGroupPoints F M) :=
    parameterPower F P (-halfModulusParameter F P) (map F M P l m) *
      v (map F P G p (map F M P l m) * g)
  have hm : Continuous (fun z : H × AdelicGroupPoints F M => map F M P l z.2) :=
    (map F M P l).continuous.comp continuous_snd
  have hf : Continuous (Function.uncurry f) :=
    ((continuous_parameterPower _).comp hm).mul
      (hc.comp (((map F P G p).continuous.comp hm).mul continuous_fst))
  refine LeftCosetSpace.continuous_out_of_invariant Γ f hf (fun g => ?_)
  refine LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
    (Δ := rationalSubgroup F M) (f g) ?_ ?_
  · intro a ha m
    have hcancel : parameterPower F P (-halfModulusParameter F P) (map F M P l a) *
        parameterPower F P (halfModulusParameter F P) (map F M P l a) = 1 := by
      rw [← parameterPower_add, neg_add_cancel, parameterPower_zero]
    dsimp only [f]
    rw [form_canonical_mul he ha, map_mul (map F M P l) a m, parameterPower_mul]
    rw [mul_mul_mul_comm, hcancel, one_mul]
  · intro a ha m
    dsimp only [f]
    rw [parameterPower_map_mul_left _ l (rationalSubgroup_le_normOneSubgroup F M ha),
      form_rational_mul hi ha]

set_option maxHeartbeats 600000 in
private theorem normWeight_right_levi_factor [LocallyOfFiniteType G.X.hom]
    [IsIso (subgroupMultiplication l iU)]
    (hU : (SubgroupFunctor.range iU).IsNormal) {v : H → ℂ}
    (hv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) v)
    (he : IsSplitComponentEquivariant p l v) (q : AdelicGroupPoints F P) (k : H) (m : Qlevi) :
    normWeight p l v (map F P G p q * k) m.out =
      ‖parameterPower F P (modulusParameter F P) (map F M P l (leviComponent l iU q))‖ *
        normWeight p l v k (LeftCosetSpace.rightTranslate Γ (leviComponent l iU q) m).out := by
  let a : AdelicGroupPoints F M := leviComponent l iU q
  let n : AdelicGroupPoints F U := radicalComponent l iU q
  let ma := map F M P l (m.out * a)
  have hq : map F M P l a * map F U P iU n = q := leviComponent_mul_radicalComponent l iU q
  have hmem : map F P G p (map F U P iU n) ∈ parabolicUnipotentImage F p iU :=
    ⟨n, map_comp_apply_of_hom iU n⟩
  have hnorm : map F P G p ma * map F P G p (map F U P iU n) * (map F P G p ma)⁻¹ ∈
      parabolicUnipotentImage F p iU :=
    conj_mem_adelicPoints_range p iU hU ma hmem
  have hnorm' := Subgroup.mem_sup_left (T := parabolicLeviRationalImage F p l) hnorm
  have hval : v (map F P G p (map F M P l m.out) * (map F P G p q * k)) =
      v (map F P G p ma * k) := by
    calc
      _ = v ((map F P G p ma * map F P G p (map F U P iU n) * (map F P G p ma)⁻¹) *
          (map F P G p ma * k)) := by
        congr 1
        rw [← hq]
        simp only [ma, map_mul]
        group
      _ = _ := hv _ hnorm' _
  have hW (g : H) := LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
    (Δ := rationalSubgroup F M) (normWeight p l v g)
    (fun x hx m => normWeight_splitComponent_mul he hx g m)
    (fun x hx m => normWeight_rational_mul (fun b hb => hv b (Subgroup.mem_sup_right hb)) hx g m)
  have hout : normWeight p l v k (LeftCosetSpace.rightTranslate Γ a m).out =
      normWeight p l v k (m.out * a) := by
    have hmk : LeftCosetSpace.mk Γ m.out = m := Quotient.out_eq m
    conv_lhs => rw [← hmk, LeftCosetSpace.rightTranslate_mk]
    exact LeftCosetSpace.out_mk_of_invariant Γ (normWeight p l v k) (hW k) (m.out * a)
  change normWeight p l v (map F P G p q * k) m.out =
    ‖parameterPower F P (modulusParameter F P) (map F M P l a)‖ * _
  rw [hout, normWeight, normWeight, hval, map_mul (map F M P l) m.out a, parameterPower_mul, norm_mul]
  have hc : ‖parameterPower F P (modulusParameter F P) (map F M P l a)‖ *
      ‖parameterPower F P (-modulusParameter F P) (map F M P l a)‖ = 1 := by
    rw [← norm_mul, ← parameterPower_add, add_neg_cancel, parameterPower_zero, norm_one]
  have hma : map F M P l m.out * map F M P l a = ma := (map_mul (map F M P l) m.out a).symm
  rw [hma]
  linear_combination -‖parameterPower F P (-modulusParameter F P) (map F M P l m.out)‖ *
    ‖v (map F P G p ma * k)‖ ^ 2 * hc

end Normalization

/-- Square integrability in the actual Iwasawa coordinates is preserved by convolution with a
continuous compactly supported kernel, for every complex parameter. -/
def InducedConvolutionWeightedSquareStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K),
    IsConnectedReductive M → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsIso (subgroupMultiplication l iU) → ∀ (φ v : AdelicGroupPoints F G → ℂ),
    Continuous φ → HasCompactSupport φ → Continuous v →
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) v →
    IsSplitComponentEquivariant p l v →
    let measure := (compactHaarProbability F G K hK.isCompact).prod
      (RestrictionSplitCentre.canonicalMeasure F M)
    let weight (f : AdelicGroupPoints F G → ℂ)
        (z : K × RestrictionSplitCentre.CanonicalQuotient F M) := normWeight p l f z.1 z.2.out
    Integrable (weight v) measure →
    ∀ lam : ComplexCharacterParameter F P, Integrable (weight (hK.inducedConvolution lam φ v)) measure

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency true in
/-- Compact Iwasawa integration, right invariance of the Levi measure, and Cauchy–Schwarz
establish the weighted square bound. -/
theorem inducedConvolutionWeightedSquare : InducedConvolutionWeightedSquareStatement := by
  intro F _ _ G P M U _ _ _ _ _ _ p _ iU l K hK hM hU hIso φ v hφ hsupp hv hleft hsplit
    measure weight hsq lam
  classical
  let : IsIso (subgroupMultiplication l iU) := hIso
  let Gpts := AdelicGroupPoints F G
  let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
  let Qlevi := RestrictionSplitCentre.CanonicalQuotient F M
  let mk := compactHaarProbability F G K hK.isCompact
  let mm := RestrictionSplitCentre.canonicalMeasure F M
  let : BorelSpace Qlevi := RestrictionSplitCentre.canonicalQuotient_borelSpace F M
    centralSplitTorusCharacter hM
  let : IsFiniteMeasure mm := RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume F M hM _ _
    (RestrictionSplitCentre.isSplitComponent_canonicalRestrictionComponent F M)
  let : IsProbabilityMeasure mk := compactHaarProbability_isProbabilityMeasure F G K hK.isCompact
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let : BorelSpace K := inferInstanceAs (BorelSpace (K : Set Gpts))
  let : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set Gpts))
  let Pimg := (map F P G p).toMonoidHom.range
  have hp := isClosedEmbedding_map F P G p
  have hPg : IsClosed (Pimg : Set Gpts) := hp.isClosed_range
  let pe : AdelicGroupPoints F P ≃ₜ Pimg := hp.isEmbedding.toHomeomorph
  let : LocallyCompactSpace Pimg := hPg.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology Pimg := inferInstanceAs (SecondCountableTopology (Pimg : Set Gpts))
  let : BorelSpace Pimg := inferInstanceAs (BorelSpace (Pimg : Set Gpts))
  let mp : Measure Pimg := Measure.haar
  let haar : Measure Gpts := Measure.haar
  let prodMap (z : Pimg × K) : Gpts := (z.1 : Gpts) * (z.2 : Gpts)
  have hprod : Continuous prodMap :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hPK (g : Gpts) : ∃ q ∈ Pimg, ∃ k ∈ K, g = q * k := by
    obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
    exact ⟨_, ⟨q, rfl⟩, k, hk, rfl⟩
  obtain ⟨c, hc, hhaar⟩ := Langlands.CompactFactorization.exists_pos_eq_smul_map_mul_prod
    haar Pimg hPg K hK.isCompact hPK mp mk
  let D : Set Pimg := Subtype.val ⁻¹' (((K : Set Gpts) * tsupport φ) * (K : Set Gpts)⁻¹)
  have hD : IsCompact D := hPg.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hK.isCompact.mul hsupp).mul hK.isCompact.inv)
  let restrictedP := mp.restrict D
  have : IsFiniteMeasure restrictedP := ⟨by simpa [restrictedP, Measure.restrict_apply_univ] using
    (hD.measure_lt_top : mp D < ⊤)⟩
  let restricted := restrictedP.prod mk
  have hrestrict : (mp.prod mk).restrict (D ×ˢ (univ : Set K)) = restricted := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hsuppP (k : K) (z : Pimg × K) (hz : z.1 ∉ D) : φ ((k : Gpts)⁻¹ * prodMap z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    apply hz
    refine ⟨(k : Gpts) * ((k : Gpts)⁻¹ * prodMap z),
      ⟨k, k.property, _, hh, rfl⟩, (z.2 : Gpts)⁻¹,
      inv_mem_inv.mpr z.2.property, ?_⟩
    simp [prodMap, mul_assoc]
  let V := normalizedValue p l v
  have hV : Continuous (Function.uncurry V) := continuous_normalizedValue p l iU hv hleft hsplit
  let s (z : Pimg × (K × Qlevi)) : ℝ := ‖V (prodMap (z.1, z.2.1)) z.2.2‖ ^ 2
  have hs : Continuous s := (hV.comp
    ((hprod.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))).norm.pow 2
  let d (q : Pimg) : ℝ := ‖parameterPower F P (modulusParameter F P)
    (map F M P l (map F P M (leviRetraction l iU hU.1.isNormal) (pe.symm q)))‖
  have hd : Continuous d := ((continuous_parameterPower _).comp
    ((map F M P l).continuous.comp
      ((map F P M (leviRetraction l iU hU.1.isNormal)).continuous.comp pe.symm.continuous))).norm
  have hs' (q : Pimg) (z : K × Qlevi) : s (q, z) =
      d q * weight v (z.1, LeftCosetSpace.rightTranslate Γ (leviComponent l iU (pe.symm q)) z.2) := by
    have hpoint : map F P G p (pe.symm q) = (q : Gpts) :=
      congrArg Subtype.val (pe.apply_symm_apply q)
    change ‖V ((q : Gpts) * ↑z.1) z.2‖ ^ 2 = _
    rw [norm_sq_normalizedValue, ← hpoint, normWeight_right_levi_factor p l iU hU.1.isNormal hleft hsplit]
    have hL (x : AdelicGroupPoints F P) : map F P M (leviRetraction l iU hU.1.isNormal) x =
        leviComponent l iU x := comp_leviRetraction l iU hU.1.isNormal x
    rw [show d q = ‖parameterPower F P (modulusParameter F P)
      (map F M P l (leviComponent l iU (pe.symm q)))‖ by simp only [d, hL]]
  have hsqProd : Integrable s (restrictedP.prod (mk.prod mm)) := by
    have htrans (q : Pimg) : MeasurePreserving
        (Prod.map (id : K → K) (LeftCosetSpace.rightTranslate Γ (leviComponent l iU (pe.symm q))))
        (mk.prod mm) (mk.prod mm) :=
      (MeasurePreserving.id mk).prod (RestrictionSplitCentre.canonicalMeasure_rightInvariant F M
        centralSplitTorusCharacter hM _)
    have hi (q : Pimg) : Integrable (fun z : K × Qlevi => s (q, z)) (mk.prod mm) :=
      ((htrans q).integrable_comp_of_integrable hsq).const_mul (d q) |>.congr
        (Eventually.of_forall fun z => (hs' q z).symm)
    refine (integrable_prod_iff hs.aestronglyMeasurable).mpr ⟨Eventually.of_forall hi, ?_⟩
    have hdI : Integrable d restrictedP := hd.continuousOn.integrableOn_compact hD
    have heq (q : Pimg) : (∫ z : K × Qlevi, ‖s (q, z)‖ ∂(mk.prod mm)) =
        d q * ∫ z : K × Qlevi, weight v z ∂(mk.prod mm) := by
      let T := Prod.map (id : K → K) (LeftCosetSpace.rightTranslate Γ (leviComponent l iU (pe.symm q)))
      have hT := htrans q
      have ha : AEStronglyMeasurable (weight v) ((mk.prod mm).map T) := by
        rw [hT.map_eq]
        exact hsq.aestronglyMeasurable
      calc
        _ = ∫ z : K × Qlevi, d q * weight v (T z) ∂(mk.prod mm) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => (Real.norm_of_nonneg (sq_nonneg _)).trans (hs' q z)
        _ = d q * ∫ z : K × Qlevi, weight v (T z) ∂(mk.prod mm) := integral_const_mul _ _
        _ = _ := by rw [← integral_map hT.measurable.aemeasurable ha, hT.map_eq]
    exact (hdI.mul_const _).congr (Eventually.of_forall fun q => (heq q).symm)
  let Dom := (K × Qlevi) × (Pimg × K)
  let f (z : Dom) : ℂ :=
    φ ((z.1.1 : Gpts)⁻¹ * prodMap z.2) * hK.heightPower lam (prodMap z.2) * V (prodMap z.2) z.1.2
  have hDomK : Continuous (fun z : Dom => (z.1.1 : Gpts)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hDomP : Continuous (fun z : Dom => prodMap z.2) := hprod.comp continuous_snd
  have hDomM : Continuous (fun z : Dom => z.1.2) := continuous_snd.comp continuous_fst
  have hVdom : Continuous (fun z : Dom => V (prodMap z.2) z.1.2) := by
    change Continuous (Function.uncurry V ∘ fun z : Dom => (prodMap z.2, z.1.2))
    exact hV.comp (hDomP.prodMk hDomM)
  have hφdom : Continuous (fun z : Dom => φ ((z.1.1 : Gpts)⁻¹ * prodMap z.2)) :=
    hφ.comp (hDomK.inv.mul hDomP)
  have hpowdom : Continuous (fun z : Dom => hK.heightPower lam (prodMap z.2)) :=
    (hK.continuous_heightPower lam).comp hDomP
  have hf : Continuous f := (hφdom.mul hpowdom).mul hVdom
  have hsqF : Integrable (fun z => ‖f z‖ ^ 2) ((mk.prod mm).prod restricted) := by
    let perm (z : (K × Qlevi) × (Pimg × K)) : K × (Pimg × (K × Qlevi)) :=
      (z.1.1, (z.2.1, (z.2.2, z.1.2)))
    have hperm : MeasurePreserving perm ((mk.prod mm).prod restricted)
        (mk.prod (restrictedP.prod (mk.prod mm))) :=
      ((MeasurePreserving.id mk).prod ((measurePreserving_prodAssoc restrictedP mk mm).comp
        Measure.measurePreserving_swap)).comp (measurePreserving_prodAssoc mk mm restricted)
    have hi' : Integrable (fun z : (K × Qlevi) × (Pimg × K) => s (perm z).2)
        ((mk.prod mm).prod restricted) := by
      simpa only [one_mul, Function.comp_def] using hperm.integrable_comp_of_integrable
        ((integrable_const («μ» := mk) (1 : ℝ)).mul_prod hsqProd)
    obtain ⟨A, hA⟩ := hsupp.exists_bound_of_continuous hφ
    have hC : IsCompact (prodMap '' (D ×ˢ (univ : Set K))) := (hD.prod isCompact_univ).image hprod
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hK.continuous_heightPower lam).continuousOn
    refine (hi'.const_mul ((max A 0 * max B 0) ^ 2)).mono' (hf.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hz : z.2.1 ∈ D
    · rw [← mul_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      unfold f
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul ((hA _).trans (le_max_left _ _))
        ((hB _ ⟨z.2, ⟨hz, mem_univ _⟩, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
    · simp only [f, hsuppP z.1.1 z.2 hz, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  let result := hK.inducedConvolution lam φ v
  have hnormalized (w : K × Qlevi) : normalizedValue p l result w.1 w.2 =
      (c : ℝ) • (∫ z, f (w, z) ∂restricted) := by
    let m := w.2.out
    let x := map F P G p (map F M P l m)
    let t := parameterPower F P (-halfModulusParameter F P) (map F M P l m)
    have hw : (w.1 : Gpts) ∈ K := w.1.property
    change t * hK.inducedConvolution lam φ v (x * (w.1 : Gpts)) = _
    rw [hK.inducedConvolution_mul_right_of_mem lam φ v hw]
    let term (g : Gpts) := φ ((w.1 : Gpts)⁻¹ * g) * hK.heightPower lam g * V g w.2
    have ht (g : Gpts) : t * (φ ((w.1 : Gpts)⁻¹ * g) * hK.inducedRightTranslate lam g v x) =
        term g := by
      have hx : hK.height (x * g) - hK.height x = hK.height g := by
        change hK.height (map F P G p (map F M P l m) * g) -
          hK.height (map F P G p (map F M P l m)) = _
        rw [hK.height_map_mul, hK.height_map, add_sub_cancel_left]
      rw [hK.inducedRightTranslate_eq_mul_exp_sub, hx]
      unfold term V normalizedValue
      change t * (φ ((w.1 : Gpts)⁻¹ * g) * (v (x * g) * hK.heightPower lam g)) =
        φ ((w.1 : Gpts)⁻¹ * g) * hK.heightPower lam g * (t * v (x * g))
      ring
    have hVw : Continuous (fun g : Gpts => V g w.2) := by
      change Continuous (Function.uncurry V ∘ fun g : Gpts => (g, w.2))
      exact hV.comp (continuous_id.prodMk continuous_const)
    have hφw : Continuous (fun g : Gpts => φ ((w.1 : Gpts)⁻¹ * g)) :=
      hφ.comp (continuous_const.mul continuous_id)
    have hterm : Continuous term := (hφw.mul (hK.continuous_heightPower lam)).mul hVw
    change t * (∫ g, φ ((w.1 : Gpts)⁻¹ * g) * hK.inducedRightTranslate lam g v x ∂haar) = _
    rw [← integral_const_mul t]
    rw [show (fun g => t * (φ ((w.1 : Gpts)⁻¹ * g) *
      hK.inducedRightTranslate lam g v x)) = term from funext ht]
    have hhaar' : haar = c • Measure.map prodMap (mp.prod mk) := hhaar
    rw [hhaar', integral_smul_nnreal_measure, integral_map hprod.measurable.aemeasurable
      hterm.aestronglyMeasurable, ← hrestrict]
    congr 1
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hz' : z.1 ∉ D := fun hh => hz ⟨hh, mem_univ _⟩
      change φ ((w.1 : Gpts)⁻¹ * prodMap z) * _ * _ = 0
      rw [hsuppP _ _ hz', zero_mul, zero_mul])).symm
  have hi := (integrable_sq_norm_integral_of_prod (mk.prod mm) restricted hf.aestronglyMeasurable
    hsqF).const_mul ((c : ℝ) ^ 2)
  refine hi.congr (Eventually.of_forall fun w => ?_)
  change (c : ℝ) ^ 2 * ‖∫ z, f (w, z) ∂restricted‖ ^ 2 = normWeight p l result w.1 w.2.out
  rw [← norm_sq_normalizedValue, hnormalized, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg c.coe_nonneg, mul_pow]

end Langlands.Global.AdelicGroupPoints
