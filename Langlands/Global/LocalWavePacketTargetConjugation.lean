import Langlands.Global.LocalWavePacketParabolicIsoTransport
import Langlands.Global.AdelicStandardWavePacketTransport
import Langlands.Global.AdelicIntertwiningConjugateTarget
import Langlands.Global.AdelicSubgroupNormalizedHaarTransport
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.Global.AdelicInducedL2Inner

/-! # Transport of the truncated limit along rational conjugation of the second parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

section Weyl

variable {F : Type} [Field F] {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {l' : M' ⟶ Q}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}

/-- A Weyl conjugation into the conjugate `q ≫ Int(s)` by `w` is a Weyl conjugation into `q`
by `s⁻¹ w`. -/
theorem AdelicGroupPoints.IsWeylConjugation.of_conjugate_target
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (h : IsWeylConjugation p l (q ≫ (G.innerIso s).hom) l' w c) :
    IsWeylConjugation p l q l' (s⁻¹ * w) c := by
  refine ⟨h.isIso, ?_⟩
  rw [h.comp_eq, innerIso_mul_inv, innerIso_inv_point_inv]
  simp only [Category.assoc]

/-- A Weyl conjugation into `q` by `w` is a Weyl conjugation into `q ≫ Int(s)` by `s w`. -/
theorem AdelicGroupPoints.IsWeylConjugation.conjugate_target
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (h : IsWeylConjugation p l q l' w c) :
    IsWeylConjugation p l (q ≫ (G.innerIso s).hom) l' (s * w) c := by
  refine ⟨h.isIso, ?_⟩
  rw [h.comp_eq, innerIso_mul_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end Weyl

section Parameters

variable {F : Type} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- The pairing of an imaginary parameter `i x` with a log vector is `i` times the real
pairing. -/
theorem complexParameterPairing_imaginaryParameter (x : RealCharacterParameter F H)
    (y : RealCharacterDual F H) :
    complexParameterPairing F H (imaginaryParameter F H x) y =
      Complex.I * (realParameterPairing F H x y : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change complexParameterPairing F H (((r : ℂ) * Complex.I) ⊗ₜ[ℤ] χ) y = _
    simp only [complexParameterPairing_tmul, realParameterPairing_tmul, Complex.ofReal_mul]
    ring
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Complex.ofReal_add, mul_add]

/-- Imaginary parameters have parameter powers of absolute value one. -/
theorem norm_parameterPower_imaginaryParameter (x : RealCharacterParameter F H)
    (g : AdelicGroupPoints F H) : ‖parameterPower F H (imaginaryParameter F H x) g‖ = 1 := by
  rw [parameterPower, complexParameterPairing_imaginaryParameter, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The product of a parameter power at an imaginary parameter with its complex conjugate. -/
theorem parameterPower_imaginaryParameter_mul_conj (x : RealCharacterParameter F H)
    (g : AdelicGroupPoints F H) :
    parameterPower F H (imaginaryParameter F H x) g *
      (starRingEnd ℂ) (parameterPower F H (imaginaryParameter F H x) g) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_parameterPower_imaginaryParameter]
  norm_num

/-- Parameter powers at a point and at its inverse are inverse. -/
theorem parameterPower_mul_parameterPower_inv (lam : ComplexCharacterParameter F H)
    (g : AdelicGroupPoints F H) :
    parameterPower F H lam g * parameterPower F H lam g⁻¹ = 1 := by
  rw [← InducedInnerProductSesquilinear.parameterPower_mul, mul_inv_cancel]
  simp [parameterPower, characterLog_one]

end Parameters

section Conjugation

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} {K : Subgroup (AdelicGroupPoints F G)}
  {p₁ p₂ : P ⟶ G} {t : AdelicGroupPoints F G}

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
theorem monoidHom_map_comp_of_conjugate_map
    (hmap : ∀ x, map F P G p₂ x = t * map F P G p₁ x * t⁻¹)
    {H : GroupScheme (Spec (CommRingCat.of F))} (j : H ⟶ P) :
    (map F H G (j ≫ p₂)).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (map F H G (j ≫ p₁)).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  change map F H G (j ≫ p₂) x = t * map F H G (j ≫ p₁) x * t⁻¹
  rw [map_comp_apply_of_hom, map_comp_apply_of_hom, hmap]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- Conjugation of the embedding conjugates the subgroup `U(𝔸) M(F)`. -/
theorem parabolicQuotientSubgroup_of_conjugate_map
    (hmap : ∀ x, map F P G p₂ x = t * map F P G p₁ x * t⁻¹) :
    parabolicQuotientSubgroup F p₂ iU l =
      (parabolicQuotientSubgroup F p₁ iU l).map (MulAut.conj t).toMonoidHom := by
  simp only [parabolicQuotientSubgroup, parabolicUnipotentImage, parabolicLeviRationalImage,
    Subgroup.map_sup, MonoidHom.map_range, monoidHom_map_comp_of_conjugate_map hmap,
    MonoidHom.comp_assoc]

open InducedInnerProductSesquilinear in
/-- Square integrable induced forms for `p₁` give, after left translation by `t⁻¹`, square
integrable induced forms for an embedding `p₂` conjugate to `p₁` by `t`. -/
theorem IsSquareIntegrableInducedForm.of_conjugate_map {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (r₀ : ParabolicRootPresentation p₁ l a) (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hG : IsConnectedReductive G) (hK₁ : IsIwasawaCompact p₁ K) (hK₂ : IsIwasawaCompact p₂ K)
    (hmap : ∀ x, map F P G p₂ x = t * map F P G p₁ x * t⁻¹) {v : AdelicGroupPoints F G → ℂ}
    (hv : IsSquareIntegrableInducedForm K hK₁.isCompact rho hsmooth hcalc p₁ iU l v) :
    IsSquareIntegrableInducedForm K hK₂.isCompact rho hsmooth hcalc p₂ iU l
      (fun x => v (t⁻¹ * x)) := by
  classical
  let v' : AdelicGroupPoints F G → ℂ := fun x => v (t⁻¹ * x)
  refine ⟨?_, ?_, ?_⟩
  · rw [parabolicQuotientSubgroup_of_conjugate_map hmap]
    simpa only [inv_inv] using hv.1.leftTranslate hcalc t⁻¹
  · intro x hx g
    change v' (map F P G p₂ (map F M P l x) * g) = _
    simp only [v', hmap]
    rw [show t⁻¹ * ((t * map F P G p₁ (map F M P l x) * t⁻¹) * g) =
      map F P G p₁ (map F M P l x) * (t⁻¹ * g) by group]
    exact hv.2.1 x hx _
  · let μK := compactHaarProbability F G K hK₁.isCompact
    let μM := RestrictionSplitCentre.canonicalMeasure F M
    let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
    let w (m : AdelicGroupPoints F M) :=
      ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖
    let W (k : K) (m : AdelicGroupPoints F M) := normWeight p₁ l v k m
    have hW (k : K) : ∀ x ∈ Γ, ∀ m, W k (x * m) = W k m := by
      apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
        (Δ := rationalSubgroup F M)
      · exact fun x hx m => normWeight_splitComponent_mul hv.2.1 hx k m
      · exact fun x hx m => normWeight_rational_mul
          (fun a ha => hv.1.1 a (Subgroup.mem_sup_right ha)) hx k m
    obtain ⟨q, k, hk, htk⟩ := hK₁.exists_eq t⁻¹
    let k₀ : K := ⟨k, hk⟩
    let : Smooth G.X.hom := hG.smooth
    let : IsIso (subgroupMultiplication l iU) := r₀.isIso_subgroupMultiplication_of_radical hRad
    let m₀ : AdelicGroupPoints F M := (leviComponent l iU q⁻¹)⁻¹
    let u₀ : AdelicGroupPoints F U := (radicalComponent l iU q⁻¹)⁻¹
    have hq : q = map F U P iU u₀ * map F M P l m₀ := by
      have hh : map F M P l (leviComponent l iU q⁻¹) *
          map F U P iU (radicalComponent l iU q⁻¹) = q⁻¹ :=
        leviComponent_mul_radicalComponent l iU q⁻¹
      dsimp only [m₀, u₀]
      rw [map_inv, map_inv, ← mul_inv_rev, hh, inv_inv]
    let T : K × LeftCosetSpace Γ → K × LeftCosetSpace Γ :=
      Prod.map (k₀ * ·) (LeftCosetSpace.rightTranslate Γ m₀)
    have hM := r₀.isCompatible.levi.isConnectedReductive
    let : IsFiniteMeasure μM :=
      RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume F M hM _ _
        (RestrictionSplitCentre.isSplitComponent_canonicalRestrictionComponent F M)
    have hT : MeasurePreserving T (μK.prod μM) (μK.prod μM) :=
      (measurePreserving_mul_left μK k₀).prod
        (RestrictionSplitCentre.canonicalMeasure_rightInvariant F M centralSplitTorusCharacter hM m₀)
    have hWi : Integrable (fun z : K × LeftCosetSpace Γ => W z.1 z.2.out) (μK.prod μM) := hv.2.2
    have hTm := (hT.integrable_comp_of_integrable hWi).const_mul (w m₀)⁻¹
    refine hTm.congr (Filter.Eventually.of_forall fun z => ?_)
    have hw (m : AdelicGroupPoints F M) : w (m * m₀) = w m * w m₀ := by
      simp only [w, map_mul, parameterPower_mul, norm_mul]
    have hw₀ : w m₀ ≠ 0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
    have hWout : W (k₀ * z.1) (LeftCosetSpace.rightTranslate Γ m₀ z.2).out =
        W (k₀ * z.1) (z.2.out * m₀) := by
      conv_lhs => rw [← LeftCosetSpace.mk_out Γ z.2, LeftCosetSpace.rightTranslate_mk]
      exact LeftCosetSpace.out_mk_of_invariant Γ (W (k₀ * z.1)) (hW (k₀ * z.1)) _
    have hu : map F P G p₁ (map F U P iU u₀) ∈
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p₁)) :=
      ⟨u₀, map_comp_apply_of_hom iU u₀⟩
    have hu' := conj_mem_adelicPoints_range p₁ iU hRad.1.isNormal (map F M P l z.2.out) hu
    have hvU : map F P G p₁ (map F M P l z.2.out) * map F P G p₁ (map F U P iU u₀) *
        (map F P G p₁ (map F M P l z.2.out))⁻¹ ∈ parabolicQuotientSubgroup F p₁ iU l := by
      obtain ⟨u, hu'⟩ := hu'
      exact Subgroup.mem_sup_left ⟨u, hu'⟩
    have hv' : v' (map F P G p₂ (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) =
        v (map F P G p₁ (map F M P l (z.2.out * m₀)) * (↑(k₀ * z.1) : AdelicGroupPoints F G)) := by
      simp only [v', hmap, Subgroup.coe_mul, map_mul]
      rw [show t⁻¹ * ((t * map F P G p₁ (map F M P l z.2.out) * t⁻¹) * ↑z.1) =
        map F P G p₁ (map F M P l z.2.out) * t⁻¹ * ↑z.1 by group, ← htk, hq, map_mul]
      rw [show map F P G p₁ (map F M P l z.2.out) *
          ((map F P G p₁ (map F U P iU u₀) * map F P G p₁ (map F M P l m₀)) * k) * ↑z.1 =
          (map F P G p₁ (map F M P l z.2.out) * map F P G p₁ (map F U P iU u₀) *
            (map F P G p₁ (map F M P l z.2.out))⁻¹) *
          ((map F P G p₁ (map F M P l z.2.out) * map F P G p₁ (map F M P l m₀)) *
            (k * ↑z.1)) by group, hv.1.1 _ hvU]
    change (w m₀)⁻¹ * W (k₀ * z.1) (LeftCosetSpace.rightTranslate Γ m₀ z.2).out =
      w z.2.out * ‖v' (map F P G p₂ (map F M P l z.2.out) * ↑z.1)‖ ^ 2
    rw [hWout, hv']
    change (w m₀)⁻¹ * (w (z.2.out * m₀) * _) = _
    rw [hw]
    field_simp

end Conjugation

section ConjugateMeasure

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine U.X.left] in
theorem map_conjugate_target (x : AdelicGroupPoints F P) :
    map F P G (p ≫ (G.innerIso s).hom) x =
      innerAdelicPoint F G s * map F P G p x * (innerAdelicPoint F G s)⁻¹ := by
  rw [map_comp_apply_of_hom]
  exact affinePointsTarget_innerIso_hom F G s _

/-- The Haar measure on `U(𝔸)` normalized by `vol(U(F) \ U(𝔸)) = 1` is right invariant when
`U` is the geometric unipotent radical of `iU`. -/
theorem isMulRightInvariant_normalizedHaarMeasure_range (j : P ⟶ G)
    [IsClosedImmersion (iU ≫ j).hom.hom.left]
    (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j)) :
        Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ j)
    (AdelicSubgroupPoints.normalizedHaarMeasure F G
      (SubgroupFunctor.range (iU ≫ j))).IsMulRightInvariant := by
  have hclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j)) :
      Set (AdelicGroupPoints F G)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ j)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j)) :
      Set (AdelicGroupPoints F G)) := hclosed
  let : LocallyCompactSpace
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j))) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j))) :=
    hclosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iU ≫ j))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ j)
      hRad.1.smooth hRad.1.connectedSpace hRad.1.isUnipotent
  let : (Measure.haar : Measure
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ j)))).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G _
  dsimp only [AdelicSubgroupPoints.normalizedHaarMeasure]
  infer_instance

/-- An `Iwasawa`-compatible Haar measure for the conjugate `p ≫ Int(s)` gives one for `p`, after
scaling by `δ_P(m₀)⁻¹`, where `t = p(s)(u₀ m₀) k₀` is an Iwasawa decomposition of
`t = s ∈ G(F) ⊆ G(𝔸)` for the conjugate. -/
theorem IsIwasawaCompatibleMeasure.of_conjugate_target
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    [IsClosedImmersion (iU ≫ p ≫ (G.innerIso s).hom).hom.hom.left]
    (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    {u₀ : AdelicGroupPoints F U} {m₀ : AdelicGroupPoints F M} {k₀ : AdelicGroupPoints F G}
    (hk₀ : k₀ ∈ K)
    (ht : map F P G (p ≫ (G.innerIso s).hom) (map F U P iU u₀ * map F M P l m₀) * k₀ =
      innerAdelicPoint F G s)
    {μL : Measure (AdelicGroupPoints F M)} [μL.IsMulRightInvariant]
    (hμL : IsIwasawaCompatibleMeasure K hKc (p ≫ (G.innerIso s).hom) iU l μL) :
    IsIwasawaCompatibleMeasure K hKc p iU l
      (ENNReal.ofReal ‖parameterPower F P (-modulusParameter F P) (map F M P l m₀)‖ • μL) := by
  let t := innerAdelicPoint F G s
  let e := G.innerIso s
  let p₁ := p ≫ e.hom
  let ρ (m : AdelicGroupPoints F M) : ℂ :=
    parameterPower F P (-modulusParameter F P) (map F M P l m)
  let V₀ := SubgroupFunctor.range (iU ≫ p)
  let V₁ := SubgroupFunctor.range (iU ≫ p₁)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V₀ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V₁ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p₁)
  let ν₀ := AdelicSubgroupPoints.normalizedHaarMeasure F G V₀
  let ν₁ := AdelicSubgroupPoints.normalizedHaarMeasure F G V₁
  let μK := compactHaarProbability F G K hKc
  have hV : V₀ = V₁.comap e.hom :=
    SubgroupFunctor.range_eq_comap_of_iso_square e (Iso.refl U) (i := iU ≫ p) (i' := iU ≫ p₁)
      (by simp [p₁])
  obtain ⟨a, ha, -, hpres⟩ :=
    AdelicSubgroupPoints.exists_adelicSubgroupIso_of_eq_comap F e V₁ V₀ hV
  have hconj (v : AdelicSubgroupPoints.adelicPoints F G V₀) :
      (a v : AdelicGroupPoints F G) = t * (v : AdelicGroupPoints F G) * t⁻¹ :=
    (ha v).trans (affinePointsTarget_innerIso_hom F G s v)
  have hme : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  have hmap (x : AdelicGroupPoints F P) : map F P G p₁ x = t * map F P G p x * t⁻¹ :=
    map_conjugate_target s x
  have : ν₁.IsMulRightInvariant := isMulRightInvariant_normalizedHaarMeasure_range (p ≫ e.hom) hRad
  have hρmul (m m' : AdelicGroupPoints F M) : ρ (m * m') = ρ m * ρ m' := by
    simp only [ρ, map_mul, InducedInnerProductSesquilinear.parameterPower_mul]
  have hρ₀ : ρ m₀ ≠ 0 := Complex.exp_ne_zero _
  intro f
  let ft : CompactlySupportedContinuousMap (AdelicGroupPoints F G) ℂ := f.comp (Homeomorph.mulLeft t⁻¹).toCocompactMap
  have hft (x : AdelicGroupPoints F G) : ft x = f (t⁻¹ * x) := rfl
  have h1 : ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
      ∫ g, ft g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
    simp only [hft]
    exact (integral_mul_left_eq_self (fun g => f g) t⁻¹).symm
  rw [h1, hμL ft]
  let k₀' : K := ⟨k₀, hk₀⟩
  have h0 : map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀ = 1 := by
    have h := ht
    change map F P G p₁ (map F U P iU u₀ * map F M P l m₀) * k₀ = t at h
    rw [hmap, map_mul] at h
    calc map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀
        = t⁻¹ * (t * (map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀)) * t⁻¹ * k₀) := by
          group
      _ = 1 := by rw [h, inv_mul_cancel]
  let J (k : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) : ℂ :=
    ∫ u : AdelicSubgroupPoints.adelicPoints F G V₁,
      ρ m * ft ((u : AdelicGroupPoints F G) * map F P G p₁ (map F M P l m) * k) ∂ν₁
  let I (k : K) : ℂ := ∫ m, J (k : AdelicGroupPoints F G) m ∂μL
  have hclaim (k : K) :
      ∫ m, ∫ u : AdelicSubgroupPoints.adelicPoints F G V₀,
          ρ m * f ((u : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
            (k : AdelicGroupPoints F G)) ∂ν₀
        ∂(ENNReal.ofReal ‖ρ m₀‖ • μL) = I (k₀' * k) := by
    have hA (m : AdelicGroupPoints F M) :
        ∫ u : AdelicSubgroupPoints.adelicPoints F G V₀,
            ρ m * f ((u : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
              (k : AdelicGroupPoints F G)) ∂ν₀ =
          (ρ m₀)⁻¹ * J (k₀' * k : K) (m * m₀) := by
      let Y : AdelicGroupPoints F G :=
        map F P G p₁ (map F M P l (m * m₀)) * ((k₀' * k : K) : AdelicGroupPoints F G)
      let h (u : AdelicSubgroupPoints.adelicPoints F G V₁) : ℂ :=
        ρ m * ft ((u : AdelicGroupPoints F G) * Y)
      have hu : map F P G p₁ (map F U P iU u₀) ∈
          AdelicSubgroupPoints.adelicPoints F G V₁ :=
        ⟨u₀, map_comp_apply_of_hom iU u₀⟩
      have hv := conj_mem_adelicPoints_range p₁ iU hRad.1.isNormal (map F M P l m) hu
      let v : AdelicSubgroupPoints.adelicPoints F G V₁ := ⟨_, hv⟩
      calc
        _ = ∫ u : AdelicSubgroupPoints.adelicPoints F G V₀,
              (fun y : AdelicSubgroupPoints.adelicPoints F G V₁ => h (y * v)) (a u) ∂ν₀ := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [h, Y, hft, Subgroup.coe_mul, hconj, hmap, map_mul, k₀', v]
          congr 2
          calc (u : AdelicGroupPoints F G) * map F P G p (map F M P l m) * (k : AdelicGroupPoints F G)
              = (u : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
                  (map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀) *
                    (k : AdelicGroupPoints F G) := by rw [h0, mul_one]
            _ = _ := by group
        _ = ∫ y : AdelicSubgroupPoints.adelicPoints F G V₁, h (y * v) ∂ν₁ :=
          hpres.integral_comp hme (fun y => h (y * v))
        _ = ∫ y : AdelicSubgroupPoints.adelicPoints F G V₁, h y ∂ν₁ :=
          integral_mul_right_eq_self h v
        _ = _ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [h, Y, hρmul]
          field_simp
          simp only [mul_assoc]
    simp only [hA]
    rw [integral_smul_measure, integral_const_mul, integral_mul_right_eq_self
      (fun m => J (k₀' * k : K) m) m₀, ENNReal.toReal_ofReal (norm_nonneg _), Complex.real_smul,
      ofReal_norm_parameterPower_neg_modulusParameter, ← mul_assoc, mul_inv_cancel₀ hρ₀, one_mul]
  change ∫ k, I k ∂μK = _
  rw [← integral_mul_left_eq_self I k₀']
  exact integral_congr_ae (Eventually.of_forall fun k => (hclaim k).symm)

/-- The coordinates `y(m)` of `H_P(m)` are additive in `m`. -/
theorem parameterCoordinates_characterLog_mul {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (m m' : AdelicGroupPoints F M) :
    parameterCoordinates F P e (characterLog F P (map F M P l (m * m'))) =
      parameterCoordinates F P e (characterLog F P (map F M P l m)) +
        parameterCoordinates F P e (characterLog F P (map F M P l m')) := by
  funext j
  simp only [parameterCoordinates, map_mul, characterLog_mul, map_add, Pi.add_apply]

/-- Right translation by `m₀` on `M(F) \ M(𝔸)`, as a measurable equivalence. -/
def rightTranslateMeasurableEquiv (m₀ : AdelicGroupPoints F M) :
    RationalQuotient F M ≃ᵐ RationalQuotient F M where
  toFun := LeftCosetSpace.rightTranslate (rationalSubgroup F M) m₀
  invFun := LeftCosetSpace.rightTranslate (rationalSubgroup F M) m₀⁻¹
  left_inv q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F M) q
    simp only [LeftCosetSpace.rightTranslate_mk, mul_inv_cancel_right]
  right_inv q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F M) q
    simp only [LeftCosetSpace.rightTranslate_mk, inv_mul_cancel_right]
  measurable_toFun := LeftCosetSpace.measurable_rightTranslate (rationalSubgroup F M) m₀
  measurable_invFun := LeftCosetSpace.measurable_rightTranslate (rationalSubgroup F M) m₀⁻¹

/-- The induced inner product for the conjugate `p ≫ Int(s)` is the induced inner product for `p`
of the left translates by `t = s`, for the Levi measure scaled by `δ_P(m₀)⁻¹` and the weight
shifted by `y(m₀)`, where `t = p(s)(u₀ m₀) k₀` is an Iwasawa decomposition for the conjugate. -/
theorem inducedInnerProduct_conjugate_target
    (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    {u₀ : AdelicGroupPoints F U} {m₀ : AdelicGroupPoints F M} {k₀ : AdelicGroupPoints F G}
    (hk₀ : k₀ ∈ K)
    (ht : map F P G (p ≫ (G.innerIso s).hom) (map F U P iU u₀ * map F M P l m₀) * k₀ =
      innerAdelicPoint F G s)
    (μL : Measure (AdelicGroupPoints F M)) [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant]
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)
    {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (p ≫ (G.innerIso s).hom) iU l) φ)
    (hψ : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (p ≫ (G.innerIso s).hom) iU l) ψ) :
    inducedInnerProduct K hKc p l
        (ENNReal.ofReal ‖parameterPower F P (-modulusParameter F P) (map F M P l m₀)‖ • μL) e
        (fun z => β (z + parameterCoordinates F P e (characterLog F P (map F M P l m₀))))
        (fun g => φ (innerAdelicPoint F G s * g)) (fun g => ψ (innerAdelicPoint F G s * g)) =
      inducedInnerProduct K hKc (p ≫ (G.innerIso s).hom) l μL e β φ ψ := by
  let t := innerAdelicPoint F G s
  let p₁ := p ≫ (G.innerIso s).hom
  let ρ (m : AdelicGroupPoints F M) : ℂ :=
    parameterPower F P (-modulusParameter F P) (map F M P l m)
  let Γ := rationalSubgroup F M
  let hΓ := isDiscrete_rationalSubgroup F M
  let μQ := LeftCosetSpace.discreteQuotientMeasure Γ hΓ μL
  let μK := compactHaarProbability F G K hKc
  let k₀' : K := ⟨k₀, hk₀⟩
  let β' : (Fin n → ℝ) → ℝ :=
    fun z => β (z + parameterCoordinates F P e (characterLog F P (map F M P l m₀)))
  have hmap (x : AdelicGroupPoints F P) : map F P G p₁ x = t * map F P G p x * t⁻¹ :=
    map_conjugate_target s x
  have hρmul (m m' : AdelicGroupPoints F M) : ρ (m * m') = ρ m * ρ m' := by
    simp only [ρ, map_mul, InducedInnerProductSesquilinear.parameterPower_mul]
  have hρ₀ : ρ m₀ ≠ 0 := Complex.exp_ne_zero _
  have h0 : map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀ = 1 := by
    have h := ht
    change map F P G p₁ (map F U P iU u₀ * map F M P l m₀) * k₀ = t at h
    rw [hmap, map_mul] at h
    calc map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀
        = t⁻¹ * (t * (map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀)) * t⁻¹ * k₀) := by
          group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hinv {f : AdelicGroupPoints F G → ℂ}
      (hf : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p₁ iU l) f)
      (x : AdelicGroupPoints F M) (g : AdelicGroupPoints F G) :
      f (t * (map F P G p (map F M P l x) * g)) =
        f (map F P G p₁ (map F M P l (x * m₀)) * (k₀ * g)) := by
    have hu : map F P G p₁ (map F U P iU u₀) ∈
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p₁)) :=
      ⟨u₀, map_comp_apply_of_hom iU u₀⟩
    obtain ⟨u, hu'⟩ := conj_mem_adelicPoints_range p₁ iU hRad.1.isNormal (map F M P l x) hu
    have hvU : map F P G p₁ (map F M P l x) * map F P G p₁ (map F U P iU u₀) *
        (map F P G p₁ (map F M P l x))⁻¹ ∈ parabolicQuotientSubgroup F p₁ iU l :=
      Subgroup.mem_sup_left ⟨u, hu'⟩
    rw [← hf _ hvU (map F P G p₁ (map F M P l (x * m₀)) * (k₀ * g))]
    congr 1
    simp only [hmap, map_mul]
    calc t * (map F P G p (map F M P l x) * g)
        = t * (map F P G p (map F M P l x) *
            (map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀) * t⁻¹ * k₀) * g) := by
          rw [h0, mul_one]
      _ = _ := by group
  have hkernel (k : AdelicGroupPoints F G) (x : AdelicGroupPoints F M) :
      InducedInnerProductSesquilinear.kernel p l e β' (fun g => φ (t * g)) (fun g => ψ (t * g))
          k x =
        (ρ m₀)⁻¹ *
          InducedInnerProductSesquilinear.kernel p₁ l e β φ ψ (k₀ * k) (x * m₀) := by
    simp only [InducedInnerProductSesquilinear.kernel, InducedInnerProductSesquilinear.weight,
      β', ← parameterCoordinates_characterLog_mul, hinv hφ, hinv hψ]
    change _ = (ρ m₀)⁻¹ * ((_ : ℂ) * ρ (x * m₀) * _ * _)
    rw [hρmul]
    field_simp
    ring
  have hφ' : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p₁ l) φ :=
    fun x hx => hφ x (Subgroup.mem_sup_right hx)
  have hψ' : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p₁ l) ψ :=
    fun x hx => hψ x (Subgroup.mem_sup_right hx)
  have hsmul : LeftCosetSpace.discreteQuotientMeasure Γ hΓ (ENNReal.ofReal ‖ρ m₀‖ • μL) =
      ENNReal.ofReal ‖ρ m₀‖ • μQ := by
    unfold μQ LeftCosetSpace.discreteQuotientMeasure
    exact LeftCosetSpace.quotientMeasure_smul Γ μL _ _
  let E := rightTranslateMeasurableEquiv m₀
  have hpres : MeasurePreserving E μQ μQ :=
    LeftCosetSpace.measurePreserving_rightTranslate_discrete Γ hΓ μL m₀
  have hclaim (k : K) :
      ∫ x : RationalQuotient F M,
          InducedInnerProductSesquilinear.kernel p l e β' (fun g => φ (t * g))
            (fun g => ψ (t * g)) k x.out
        ∂(ENNReal.ofReal ‖ρ m₀‖ • μQ) =
      ∫ x : RationalQuotient F M,
          InducedInnerProductSesquilinear.kernel p₁ l e β φ ψ ((k₀' * k : K) : AdelicGroupPoints F G)
            x.out ∂μQ := by
    let Φ (x : AdelicGroupPoints F M) : ℂ :=
      InducedInnerProductSesquilinear.kernel p₁ l e β φ ψ (k₀ * (k : AdelicGroupPoints F G)) x
    have hΦ (x : RationalQuotient F M) : Φ (E x).out = Φ (x.out * m₀) := by
      change Φ (LeftCosetSpace.rightTranslate Γ m₀ x).out = _
      conv_lhs => rw [← LeftCosetSpace.mk_out Γ x, LeftCosetSpace.rightTranslate_mk]
      exact LeftCosetSpace.out_mk_of_invariant Γ Φ
        (fun g0 hg0 m => InducedInnerProductSesquilinear.kernel_rational_mul e β hφ' hψ' hg0 _ m) _
    change _ = ∫ x : RationalQuotient F M, Φ x.out ∂μQ
    rw [← hpres.integral_comp' (fun x => Φ x.out)]
    simp only [hΦ]
    simp only [Φ]
    rw [integral_smul_measure]
    simp only [hkernel]
    rw [integral_const_mul, ENNReal.toReal_ofReal (norm_nonneg _), Complex.real_smul,
      ofReal_norm_parameterPower_neg_modulusParameter, ← mul_assoc, mul_inv_cancel₀ hρ₀, one_mul]
  rw [InducedInnerProductSesquilinear.inducedInnerProduct_eq_kernel,
    InducedInnerProductSesquilinear.inducedInnerProduct_eq_kernel, hsmul]
  change ∫ k : K, _ ∂μK = ∫ k : K, _ ∂μK
  rw [← integral_mul_left_eq_self (fun k : K => ∫ x : RationalQuotient F M,
    InducedInnerProductSesquilinear.kernel p₁ l e β φ ψ (k : AdelicGroupPoints F G) x.out ∂μQ) k₀']
  exact integral_congr_ae (Eventually.of_forall fun k => hclaim k)

end ConjugateMeasure

section ConjugateTarget

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
  {A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom] [IsAffine M'.X.left]
  [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  {Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ}
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left] {π' : P' ⟶ M'} {a' : A'.toGrp ⟶ M'}

/-- The limit for the target `p'` gives the limit for its rational conjugate `p' ≫ Int(s)`, with
the same Levi data and the same regularity predicates. -/
theorem TruncatedWavePacketPairLimit.of_conj_target
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    [IsClosedImmersion (p' ≫ (G.innerIso s).hom).hom.hom.left]
    [IsClosedImmersion (iU' ≫ p' ≫ (G.innerIso s).hom).hom.hom.left]
    (hG : IsConnectedReductive G) (hU : IsUnipotent U)
    (r' : ParabolicRootPresentation p' l' a')
    (hRad' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact p' K)
    (hK'' : IsIwasawaCompact (p' ≫ (G.innerIso s).hom) K)
    {Reg : ℝ → ComplexCharacterParameter F P → Prop}
    {Reg' : ℝ → ComplexCharacterParameter F P' → Prop}
    (hlim : TruncatedWavePacketPairLimit K Λ p iU l hK Reg p' iU' l' π' hK' Reg') :
    TruncatedWavePacketPairLimit K Λ p iU l hK Reg (p' ≫ (G.innerIso s).hom) iU' l' π' hK''
      Reg' := by
  classical
  intro N d rho hsmooth hcalc hrho μ₂ _ hμ₂ n n' e e' β₂ hβc hβs hβ1 k q v b c S E D hv
    hb hS hc hD hE hEis k' q' v₂ b' c₂ S' E₂ D' hv₂ hb' hS' hc₂ hD' hE₂ hEis₂ T _ w₂ cw hw₂
    hinj hsurj₂ m ψ₂ coeff₂ DM hψ₂ hDM hcoeff₂ hexp₂
  let t := innerAdelicPoint F G s
  let p'' := p' ≫ (G.innerIso s).hom
  have hmap (x : AdelicGroupPoints F P') : map F P' G p'' x = t * map F P' G p' x * t⁻¹ :=
    map_conjugate_target s x
  have hmap' (x : AdelicGroupPoints F P') :
      map F P' G p' x = t⁻¹ * map F P' G p'' x * t⁻¹⁻¹ := by
    rw [hmap]
    group
  obtain ⟨qa, k₀, hk₀, htq⟩ := hK''.exists_eq t
  let : Smooth G.X.hom := hG.smooth
  let : IsIso (subgroupMultiplication l' iU') := r'.isIso_subgroupMultiplication_of_radical hRad'
  let m₀ : AdelicGroupPoints F M' := (leviComponent l' iU' qa⁻¹)⁻¹
  let u₀ : AdelicGroupPoints F U' := (radicalComponent l' iU' qa⁻¹)⁻¹
  have hq : qa = map F U' P' iU' u₀ * map F M' P' l' m₀ := by
    have hh : map F M' P' l' (leviComponent l' iU' qa⁻¹) *
        map F U' P' iU' (radicalComponent l' iU' qa⁻¹) = qa⁻¹ :=
      leviComponent_mul_radicalComponent l' iU' qa⁻¹
    dsimp only [m₀, u₀]
    rw [map_inv, map_inv, ← mul_inv_rev, hh, inv_inv]
  have ht : map F P' G p'' (map F U' P' iU' u₀ * map F M' P' l' m₀) * k₀ = t := by
    rw [← hq]
    exact htq
  have hheight (lam : ComplexCharacterParameter F P') :
      hK''.heightPower lam t = parameterPower F P' lam qa := by
    rw [IsIwasawaCompact.heightPower, hK''.height_eq hk₀ htq, parameterPower]
  have hpp (lam : ComplexCharacterParameter F P') :
      parameterPower F P' lam qa⁻¹ * parameterPower F P' lam qa = 1 := by
    rw [mul_comm, parameterPower_mul_parameterPower_inv]
  have hpneg (lam : ComplexCharacterParameter F P') :
      parameterPower F P' lam qa * parameterPower F P' (-lam) qa = 1 := by
    simp only [parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero]
  -- the Levi measure
  have hM' := r'.isCompatible.levi.isConnectedReductive
  have : μ₂.IsMulRightInvariant := by
    have := adelicHaarUnimodularity.{0}.2 F M' hM'
    rw [Measure.isMulLeftInvariant_eq_smul μ₂ Measure.haar]
    infer_instance
  let ρ₀ : ℂ := parameterPower F P' (-modulusParameter F P') (map F M' P' l' m₀)
  have hρ₀ : ρ₀ ≠ 0 := Complex.exp_ne_zero _
  let μ₁ : Measure (AdelicGroupPoints F M') := ENNReal.ofReal ‖ρ₀‖ • μ₂
  have : μ₁.IsHaarMeasure := Measure.IsHaarMeasure.smul μ₂
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hρ₀)).ne' ENNReal.ofReal_ne_top
  have hμ₁ : IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μ₁ :=
    IsIwasawaCompatibleMeasure.of_conjugate_target s hRad' hK'.isCompact hk₀ ht hμ₂
  let y₀ := parameterCoordinates F P' e' (characterLog F P' (map F M' P' l' m₀))
  let β₁ : (Fin n' → ℝ) → ℝ := fun z => β₂ (z + y₀)
  have hβc₁ : Continuous β₁ := hβc.comp (continuous_id.add continuous_const)
  have hβs₁ : HasCompactSupport β₁ := hβs.comp_homeomorph (Homeomorph.addRight y₀)
  have hβ1₁ : ∫ z, β₁ z = 1 := by
    simp only [β₁]
    rw [integral_add_right_eq_self (fun z => β₂ z) y₀]
    exact hβ1
  -- forms
  let r'' := r'.compAmbientIso (G.innerIso s)
  have hconjform {φ : AdelicGroupPoints F G → ℂ}
      (hφ : IsSquareIntegrableInducedForm K hK''.isCompact rho hsmooth hcalc p'' iU' l' φ) :
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l'
        (fun x => φ (t * x)) := by
    simpa only [inv_inv] using
      IsSquareIntegrableInducedForm.of_conjugate_map r'' hRad' hG hK'' hK' hmap' hφ
  let v₁ (j : Fin k') (i : Fin q') (x : AdelicGroupPoints F G) : ℂ := v₂ j i (t * x)
  let ψ₁ (τ : T) (j : Fin k) (i : Fin m) (x : AdelicGroupPoints F G) : ℂ := ψ₂ τ j i (t * x)
  have hv₁ (j : Fin k') (i : Fin q') :
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v₁ j i) :=
    hconjform (hv₂ j i)
  have hψ₁ (τ : T) (j : Fin k) (i : Fin m) :
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ₁ τ j i) :=
    hconjform (hψ₂ τ j i)
  -- Eisenstein data
  let L : (Fin n' → ℝ) →ₗ[ℝ] ℂ :=
    (((complexParameterPairing F P').flip (characterLog F P' qa)).restrictScalars ℝ).comp
      ((imaginaryParameter F P').comp e'.toLinearMap)
  have hL (x : Fin n' → ℝ) :
      parameterPower F P' (imaginaryParameter F P' (e' x)) qa = Complex.exp (L x) := rfl
  let c₁ (j : Fin k') (x : Fin n' → ℝ) : ℂ :=
    c₂ j x * parameterPower F P' (imaginaryParameter F P' (e' x)) qa
  have hc₁ (j : Fin k') : ContDiff ℝ (⊤ : ℕ∞) (c₁ j) ∧ ∀ x ∉ S', c₁ j x = 0 := by
    have hLd : ContDiff ℝ (⊤ : ℕ∞) L := L.toContinuousLinearMap.contDiff
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [c₁, hL]
      exact (hc₂ j).1.mul hLd.cexp
    · simp only [c₁, (hc₂ j).2 x hx, zero_mul]
  let E₁ (j : Fin k') (lam : ComplexCharacterParameter F P') (g : AdelicGroupPoints F G) : ℂ :=
    parameterPower F P' lam qa⁻¹ * E₂ j lam g
  have hE₁ (j : Fin k') (g : AdelicGroupPoints F G) :
      IsMeromorphicInCoordinatesOn (fun lam => E₁ j lam g) D' := by
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P') := (hE₂ j g).1
    simpa only [Set.univ_inter, E₁, Pi.mul_def] using
      (isMeromorphicInCoordinatesOn_parameterPower qa⁻¹).mul (hE₂ j g)
  have hEis₁ (j : Fin k') : ∃ R : ℝ, ∀ lam, Reg' R lam → ∀ g,
      E₁ j lam g = ∑ i, b' j i lam * hK'.eisensteinSeries (v₁ j i) lam g := by
    obtain ⟨R, hR⟩ := hEis₂ j
    refine ⟨R, fun lam hlam g => ?_⟩
    have hser (i : Fin q') : hK''.eisensteinSeries (v₂ j i) lam g =
        parameterPower F P' lam qa * hK'.eisensteinSeries (v₁ j i) lam g := by
      rw [← hheight]
      have h := hK'.eisensteinSeries_conjugate_parabolic s hK'' r'.isCompatible.levi hRad'
        (hv₁ j i).1.1 lam g
      have hfun : (fun x => v₁ j i ((innerAdelicPoint F G s)⁻¹ * x)) = v₂ j i := by
        funext x
        simp only [v₁, t, mul_inv_cancel_left]
      rw [hfun] at h
      exact h
    simp only [E₁, hR lam hlam g, hser, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (b' j i lam * hK'.eisensteinSeries (v₁ j i) lam g) * hpp lam
  -- Weyl data
  let w₁ (τ : T) : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X := s⁻¹ * w₂ τ
  have hw₁ (τ : T) : IsWeylConjugation p l p' l' (w₁ τ) (cw τ) :=
    (hw₂ τ).of_conjugate_target s
  have hsurj₁ : ∀ σ ∈ weylParameterSet p l p' l' π', ∃ τ, weylParameter l (cw τ) π' = σ := by
    rintro σ ⟨w₀, c₀, hc₀, rfl⟩
    exact hsurj₂ _ ⟨s * w₀, c₀, hc₀.conjugate_target s, rfl⟩
  let coeff₁ (τ : T) (j : Fin k) (i : Fin m) (lam : ComplexCharacterParameter F P) : ℂ :=
    parameterPower F P' (weylParameter l (cw τ) π' lam) qa * coeff₂ τ j i lam
  have hcoeff₁ (τ : T) (j : Fin k) (i : Fin m) : IsMeromorphicInCoordinatesOn (coeff₁ τ j i) DM := by
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hcoeff₂ τ j i).1
    have hpw : (fun lam => parameterPower F P' (weylParameter l (cw τ) π' lam) qa) =
        fun lam => parameterPower F P lam (map F P' P (π' ≫ cw τ ≫ l) qa) := by
      funext lam
      exact parameterPower_parameterRestrict (π' ≫ cw τ ≫ l) lam qa
    have h := (isMeromorphicInCoordinatesOn_parameterPower
      (map F P' P (π' ≫ cw τ ≫ l) qa)).mul (hcoeff₂ τ j i)
    rw [← hpw] at h
    simpa only [Set.univ_inter, coeff₁, Pi.mul_def] using h
  have hexp₁ (τ : T) (j : Fin k) : ∃ R : ℝ, ∀ lam, Reg R lam → ∀ g,
      ∑ i, b j i lam *
          hK.intertwiningOperator hK' iU l iU' (cw τ) π' (w₁ τ) (v j i) lam g =
        ∑ i, coeff₁ τ j i lam * ψ₁ τ j i g := by
    obtain ⟨R, hR⟩ := hexp₂ τ j
    refine ⟨R, fun lam hlam g => ?_⟩
    have hop (i : Fin q) :
        hK.intertwiningOperator hK' iU l iU' (cw τ) π' (w₁ τ) (v j i) lam g =
          parameterPower F P' (weylParameter l (cw τ) π' lam) qa *
            hK.intertwiningOperator hK'' iU l iU' (cw τ) π' (w₂ τ) (v j i) lam (t * g) := by
      obtain ⟨-, hQ', hI⟩ := intertwiningConjugateTarget F G P M U P' M' U' p iU l p' iU' l' π'
        (w₁ τ) s (cw τ) (hw₁ τ) hU K hK hK' (v j i)
        (fun x hx g' => (hv j i).1.1 x (Subgroup.mem_sup_left hx) g')
      have h := hI lam g
      simp only [w₁, mul_inv_cancel_left] at h
      change hK.intertwiningOperator hK'' iU l iU' (cw τ) π' (w₂ τ) (v j i) lam (t * g) = _ at h
      rw [h, hheight, ← mul_assoc, hpneg, one_mul]
    simp only [hop, coeff₁, ψ₁]
    rw [← Finset.sum_congr rfl fun i _ => (mul_left_comm (b j i lam)
      (parameterPower F P' (weylParameter l (cw τ) π' lam) qa) _).symm, ← Finset.mul_sum,
      hR lam hlam (t * g), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- apply the limit for p'
  have h := hlim rho hsmooth hcalc hrho μ₁ hμ₁ e e' β₁ hβc₁ hβs₁ hβ1₁ k q v b c S E D hv hb hS hc
    hD hE hEis k' q' v₁ b' c₁ S' E₁ D' hv₁ hb' hS' hc₁ hD' hE₁ hEis₁ T w₁ cw hw₁ hinj hsurj₁ m
    ψ₁ coeff₁ DM hψ₁ hDM hcoeff₁ hexp₁
  have hΘ (x : Fin n' → ℝ) (j : Fin k') (g : AdelicGroupPoints F G) :
      c₁ j x * E₁ j (imaginaryParameter F P' (e' x)) g =
        c₂ j x * E₂ j (imaginaryParameter F P' (e' x)) g := by
    simp only [c₁, E₁]
    rw [mul_assoc, ← mul_assoc (parameterPower F P' _ qa), mul_comm (parameterPower F P' _ qa),
      hpp, one_mul]
  have hiw (τ : T) (z : RealCharacterParameter F P) :
      weylParameter l (cw τ) π' (imaginaryParameter F P z) =
        imaginaryParameter F P' (realWeylParameter l (cw τ) π' z) :=
    parameterRestrict_imaginaryParameter (π' ≫ cw τ ≫ l) z
  have hip (τ : T) (j : Fin k) (i : Fin m) (j' : Fin k') (i' : Fin q') :
      inducedInnerProduct K hK'.isCompact p' l' μ₁ e' β₁ (ψ₁ τ j i) (v₁ j' i') =
        inducedInnerProduct K hK''.isCompact p'' l' μ₂ e' β₂ (ψ₂ τ j i) (v₂ j' i') :=
    inducedInnerProduct_conjugate_target s hRad' hK'.isCompact hk₀ ht μ₂ e' β₂
      (hψ₂ τ j i).1.1 (hv₂ j' i').1.1
  have hcancel (a b₀ c₀ d₀ f₀ : ℂ) (z : RealCharacterParameter F P') :
      a * (parameterPower F P' (imaginaryParameter F P' z) qa * b₀) *
          (starRingEnd ℂ) (c₀ * parameterPower F P' (imaginaryParameter F P' z) qa) * d₀ * f₀ =
        a * b₀ * (starRingEnd ℂ) c₀ * d₀ * f₀ := by
    rw [map_mul]
    linear_combination (a * b₀ * (starRingEnd ℂ) c₀ * d₀ * f₀) *
      parameterPower_imaginaryParameter_mul_conj z qa
  simp only [hΘ] at h
  simpa only [c₁, coeff₁, LinearEquiv.apply_symm_apply, hiw, hcancel, hip] using h

end ConjugateTarget

end Langlands.Global
