import Langlands.Global.AdelicAmbientWavePacketProfileFourier
import Langlands.Global.AdelicGroupParabolicSpectrumReduction
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Global.AdelicNormOneQuotientIso
import Langlands.Global.AdelicSpectralBump
import Langlands.Global.AdelicSquareIntegrableHeightExpansion
import Langlands.Global.AdelicWavePacketUnitaryCentrePairing
import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicWeakConstantTermPairingPolynomials
import Langlands.Global.AdelicWeakConstantTermTop

/-! # Wave packets from the full standard parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

namespace StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

omit [NumberField F] in
private theorem topParabolicRepresented :
    (⊤ : SubgroupFunctor G).IsRepresentedBy (fam.p fam.top) := by
  have h := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
    fam.ν fam.generic
  rw [← (fam.isCompatible fam.top).parabolic_eq.trans h.2.2.1]
  exact (fam.isCompatible fam.top).parabolic.isClosedSubgroup.isRepresentedBy_range

omit [NumberField F] in
private theorem topLeviRepresented :
    (⊤ : SubgroupFunctor G).IsRepresentedBy (fam.l fam.top ≫ fam.p fam.top) := by
  have h := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
    fam.ν fam.generic
  rw [← (fam.isCompatible fam.top).levi_eq.trans h.2.2.2.1]
  exact ((fam.isCompatible fam.top).levi.isClosedSubgroup.comp
    (fam.isCompatible fam.top).parabolic.isClosedSubgroup).isRepresentedBy_range

omit [NumberField F] in
private def fullParameterEquiv {P : GroupScheme (Spec (CommRingCat.of F))}
    (p : P ⟶ G) [IsIso p] :
    RealCharacterParameter F G ≃ₗ[ℝ] RealCharacterParameter F P :=
  LinearEquiv.ofLinearMap (realCharacterParameterPullback p) (realCharacterParameterPullback (inv p))
    (by rw [← realCharacterParameterPullback_comp, IsIso.hom_inv_id, realCharacterParameterPullback_id])
    (by rw [← realCharacterParameterPullback_comp, IsIso.inv_hom_id, realCharacterParameterPullback_id])

variable {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}

/-- An inducing form for the full standard parabolic times a split-centre Fourier profile
is a wave packet for the given compact. The continuation is the entire one-term series. -/
theorem isWavePacket_top_ambientProfile_mul
    (hK : IsIwasawaCompact (fam.p fam.bot) K) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) φ)
    {m : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) {b : (Fin m → ℝ) → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) :
    IsWavePacket F G K rho hsmooth hcalc (fun g => ambientWavePacketProfile e b g * φ g) := by
  let J := fam.top
  let p := fam.p J
  let l := fam.l J
  let a := fam.a J
  let iU := fam.iU J
  have hp : IsClosedImmersion p.hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  have : IsIso p := by
    change IsIso (fam.p fam.top)
    rw [← fam.topParabolicRepresented.topIso_hom]
    infer_instance
  let hKJ : IsIwasawaCompact p K := fam.isIwasawaCompact_of_bot hK J
  let r : ParabolicRootPresentation p l a :=
    ⟨⟨fam.T, fam.i, fam.ν, J.1, fam.f J⟩, fam.isCompatible J⟩
  have hi : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hW : Fintype (relativeWeylGroup r.data.i) :=
    @Fintype.ofFinite _ (fam.connectedReductive.finite_relativeWeylGroup r.data.i
      r.isCompatible.maximalSplit)
  have hf : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
    have := r.isCompatible.splitComponent.isCentralSplitTorus.1.mono
    have := r.isCompatible.levi.isClosedSubgroup.mono
    have := r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ l ≫ p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
  have hA : IsSplitTorus (fam.A J).toGrp := r.isCompatible.splitComponent.1.1.1
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  obtain ⟨n, ⟨ec⟩⟩ := exists_complexParameterEquiv fam.connectedReductive r.isCompatible.parabolic
  let : FiniteDimensional ℂ (ComplexCharacterParameter F (fam.P J)) := ec.finiteDimensional
  let ep := e.trans (fullParameterEquiv p)
  let E : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ :=
    hKJ.eisensteinSeries φ
  refine ⟨fam.P J, fam.M J, fam.U J, fam.A J, fam.affineP J, fam.affineM J, fam.finiteTypeM J,
    fam.affineU J, p, hp, iU, l, fam.closedU J, a, r, hi, hW, hf, hA, hT, fam.isUnipotentRadical J,
    hKJ, m, ep, 1, fun _ => φ, fun _ => b, fun _ => E, Set.univ,
    fun _ => hφ, fun _ => ⟨hb, hbc⟩, Set.subset_univ _, ?_, fun _ => ⟨0, fun _ _ => rfl⟩, ?_⟩
  · intro j g
    exact hKJ.isMeromorphicInCoordinatesOn_eisensteinSeries_of_isIso hφ.1.1
      r.isCompatible.levi (fam.isUnipotentRadical J) g
  · funext g
    have heis (x : Fin m → ℝ) :
        E (imaginaryParameter F (fam.P J) (ep x)) g =
          φ g * parameterPower F G (imaginaryParameter F G (e x)) g := by
      change hKJ.eisensteinSeries φ (imaginaryParameter F (fam.P J) (ep x)) g = _
      rw [hKJ.eisensteinSeries_of_isIso hφ.1.1 r.isCompatible.levi (fam.isUnipotentRadical J)]
      let y := map F G (fam.P J) (inv p) g
      have hy : map F (fam.P J) G p y = g := by
        dsimp only [y]
        rw [← map_comp_apply_of_hom, IsIso.inv_hom_id]
        change g ≫ 𝟙 G.X = g
        exact Category.comp_id _
      have hH : hKJ.height g = characterLog F (fam.P J) y :=
        hy ▸ hKJ.height_map y
      change φ g * Complex.exp (complexParameterPairing F (fam.P J)
        (imaginaryParameter F (fam.P J) (realCharacterParameterPullback p (e x)))
        (hKJ.height g)) = _
      rw [hH, imaginaryParameter_pullback]
      change φ g * parameterPower F (fam.P J) (parameterRestrict p
        (imaginaryParameter F G (e x))) y = _
      rw [parameterPower_pullback, hy]
    simp only [Fin.sum_univ_one, heis, ambientWavePacketProfile]
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring

open RestrictionSplitCentre (canonicalSubgroup canonicalRationalSubgroup map_mem_canonicalSubgroup
  positiveCentreHaarMeasure)

private theorem topInducingInvariance
    (hK : IsIwasawaCompact (fam.p fam.bot) K) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) φ) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) φ ∧
      IsLeftInvariantUnder F G (canonicalSubgroup F G) φ := by
  let e := fam.topLeviRepresented.topIso
  have he : e.hom = fam.l fam.top ≫ fam.p fam.top := fam.topLeviRepresented.topIso_hom
  constructor
  · rintro _ ⟨w, rfl⟩ g
    apply hφ.1.1
    apply le_sup_right (b := parabolicLeviRationalImage F (fam.p fam.top) (fam.l fam.top))
    refine ⟨G.affinePointsTarget (inv e.hom) (CommAlgCat.of F F) w, ?_⟩
    change map F (fam.M fam.top) G (fam.l fam.top ≫ fam.p fam.top)
      (rational F (fam.M fam.top) (G.affinePointsTarget (inv e.hom) (CommAlgCat.of F F) w)) = _
    rw [← he]
    exact map_rational_inv_of_isIso (p := e.hom) w
  · intro x hx g
    let y := map F G (fam.M fam.top) e.inv x
    have hy : y ∈ canonicalSubgroup F (fam.M fam.top) := map_mem_canonicalSubgroup e.symm hx
    have hxy : map F (fam.M fam.top) G e.hom y = x := by
      dsimp only [y]
      rw [← map_comp_apply_of_hom, e.inv_hom_id]
      change x ≫ 𝟙 G.X = x
      exact Category.comp_id _
    have hred : IsConnectedReductive (fam.P fam.top) :=
      fam.connectedReductive.of_iso fam.topParabolicRepresented.topIso
    have hδ : halfModulusParameter F (fam.P fam.top) = 0 := by
      rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F _ hred,
        TensorProduct.tmul_zero]
    have h := hφ.2.1 y hy g
    rw [hδ, InducedInnerProductIntegrable.parameterPower_zero, one_mul,
      ← map_comp_apply_of_hom, ← he, hxy] at h
    exact h

private theorem topPositive_mem_canonical {x : AdelicGroupPoints F (fam.P fam.top)}
    (hx : x ∈ fam.positiveSplitComponent fam.top) :
    map F (fam.P fam.top) G (fam.p fam.top) x ∈ canonicalSubgroup F G := by
  let e := fam.topLeviRepresented.topIso
  have he : e.hom = fam.l fam.top ≫ fam.p fam.top := fam.topLeviRepresented.topIso_hom
  obtain ⟨t, ht, rfl⟩ := hx
  have hmem : map F (fam.A fam.top).toGrp (fam.M fam.top) (fam.a fam.top) t ∈
      canonicalSubgroup F (fam.M fam.top) := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup
      (fam.isCompatible fam.top).splitComponent]
    exact ⟨t, ht, rfl⟩
  have h := map_mem_canonicalSubgroup e hmem
  rw [he, ← map_comp_apply_of_hom, ← Category.assoc, map_comp_apply_of_hom] at h
  exact h

private theorem normOnePairing_top_eq_zero
    (hK : IsIwasawaCompact (fam.p fam.bot) K) {φ Φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) φ)
    (hΦ : IsLeftInvariantUnder F G (rationalSubgroup F G) Φ)
    (ν : RealCharacterParameter F G)
    (hν : ∀ x ∈ canonicalSubgroup F G, ∀ g,
      Φ (x * g) = parameterPower F G (imaginaryParameter F G ν) x * Φ g)
    (horth : ∀ Θ, IsWavePacket F G K rho hsmooth hcalc Θ →
      ∫ q : RationalQuotient F G, Φ q.out * starRingEnd ℂ (Θ q.out)
        ∂(rationalQuotientHaarMeasure F G) = 0) :
    (∫ q : NormOneRationalQuotient F G,
      φ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
        ∂(normOneRationalQuotientHaarMeasure F G)) = 0 := by
  let e := ambientParameterChart fam.connectedReductive
  let translation := Homeomorph.addRight (-(e.symm ν))
  let β := spectralBump (Module.finrank ℝ (RealCharacterParameter F G))
  let b := β.val ∘ translation
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := β.property.1.comp (contDiff_id.add contDiff_const)
  have hbc : HasCompactSupport b := β.property.2.1.comp_homeomorph translation
  have hbone : b (e.symm ν) = 1 := by
    change β.val (e.symm ν + -(e.symm ν)) = 1
    rw [add_neg_cancel]
    exact β.property.2.2
  obtain ⟨c, hc, hinv⟩ := ambientWavePacketProfileFourierInversion F G fam.connectedReductive e
  obtain ⟨_, hcValue⟩ := hinv b hb hbc ν
  have hnonzero : (∫ a : canonicalSubgroup F G,
      ambientWavePacketProfile e b a.val *
        starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)
      ∂(positiveCentreHaarMeasure F G fam.connectedReductive)) ≠ 0 := by
    rw [hcValue, hbone, mul_one]
    exact Complex.ofReal_ne_zero.mpr hc.ne'
  obtain ⟨hφrat, hφcentre⟩ := fam.topInducingInvariance hK hφ
  have hφinv : IsLeftInvariantUnder F G (canonicalRationalSubgroup F G) φ :=
    LeftCosetSpace.invariant_sup _ φ hφcentre hφrat
  let Θ : AdelicGroupPoints F G → ℂ := fun g => ambientWavePacketProfile e b g * φ g
  have hΘ : IsWavePacket F G K rho hsmooth hcalc Θ :=
    fam.isWavePacket_top_ambientProfile_mul hK hφ e hb hbc
  have hzero : (∫ q : RationalQuotient F G, Θ q.out * starRingEnd ℂ (Φ q.out)
      ∂(rationalQuotientHaarMeasure F G)) = 0 := by
    have hconj := congrArg (starRingEnd ℂ) (horth Θ hΘ)
    rw [map_zero, ← integral_conj] at hconj
    simpa only [map_mul, starRingEnd_apply, star_star, mul_comm] using hconj
  obtain ⟨_, hEq⟩ :=
    wavePacketUnitaryCentrePairing F G fam.connectedReductive e b ν φ Φ hΦ hν hφinv hnonzero
  exact (mul_eq_zero.mp (hEq.symm.trans hzero)).resolve_left hnonzero

private theorem topPairingIntegral_eq_zero_of_normOne
    (hK : IsIwasawaCompact (fam.p fam.bot) K) {φ Φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) φ)
    (hΦrat : IsLeftInvariantUnder F G (rationalSubgroup F G) Φ)
    (ν : RealCharacterParameter F G)
    (hν : ∀ x ∈ canonicalSubgroup F G, ∀ g,
      Φ (x * g) = parameterPower F G (imaginaryParameter F G ν) x * Φ g)
    (x : AdelicGroupPoints F (fam.P fam.top)) (hx : x ∈ fam.positiveSplitComponent fam.top)
    (hInt : Integrable (fam.squareIntegrablePairingIntegrand K fam.top x φ Φ)
      (fam.squareIntegrablePairingMeasure K hK.isCompact fam.top))
    (hzero : (∫ q : NormOneRationalQuotient F G,
      φ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
        ∂(normOneRationalQuotientHaarMeasure F G)) = 0) :
    (∫ z, fam.squareIntegrablePairingIntegrand K fam.top x φ Φ z
      ∂(fam.squareIntegrablePairingMeasure K hK.isCompact fam.top)) = 0 := by
  obtain ⟨hφrat, hφcentre⟩ := fam.topInducingInvariance hK hφ
  let e := fam.topLeviRepresented.topIso
  have he : e.hom = fam.l fam.top ≫ fam.p fam.top := fam.topLeviRepresented.topIso_hom
  let qIso := normOneQuotientIso e
  obtain ⟨_, _, hmeasure⟩ := normOneQuotientIsoHaar e
  have := AdelicGroupPoints.normOneHaarRightInvariant F G fam.connectedReductive.smooth
    fam.connectedReductive.connectedSpace
  let k₁ (k : K) : normOneSubgroup F G :=
    ⟨k.val, compactSubgroup_le_normOneSubgroup F G K hK.isCompact k.property⟩
  let r (k : K) := LeftCosetSpace.rightTranslateHomeomorph (rationalNormOneSubgroup F G) (k₁ k)
  let f (g : normOneSubgroup F G) : ℂ := φ g.val * starRingEnd ℂ (Φ g.val)
  let b (q : NormOneRationalQuotient F G) := f q.out
  have hleft : ∀ t ∈ rationalNormOneSubgroup F G, ∀ g, f (t * g) = f g := by
    rintro _ ⟨w, rfl⟩ g
    have hw : (rationalNormOne F G w).val ∈ rationalSubgroup F G := ⟨w, rfl⟩
    dsimp only [f, Subgroup.coe_mul]
    rw [hφrat _ hw, hΦrat _ hw]
  let a := map F (fam.P fam.top) G (fam.p fam.top) x
  have ha : a ∈ canonicalSubgroup F G := fam.topPositive_mem_canonical hx
  let shiftFactor := starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a)
  have hSection (k : K) (q : NormOneRationalQuotient F (fam.M fam.top)) :
      fam.squareIntegrablePairingIntegrand K fam.top x φ Φ (k, q) =
        shiftFactor * b (r k (qIso q)) := by
    have htr : r k (qIso q) = LeftCosetSpace.mk (rationalNormOneSubgroup F G)
        (normOnePointsIso e q.out * k₁ k) := by
      change LeftCosetSpace.rightTranslate (rationalNormOneSubgroup F G) (k₁ k)
        (normOneQuotientIso e q) = _
      have hq : LeftCosetSpace.mk (rationalNormOneSubgroup F (fam.M fam.top)) q.out = q :=
        Quotient.out_eq q
      conv_lhs => rw [← hq]
      rw [normOneQuotientIso_mk, LeftCosetSpace.rightTranslate_mk]
    rw [htr]
    change _ = shiftFactor * f (LeftCosetSpace.mk (rationalNormOneSubgroup F G)
      (normOnePointsIso e q.out * k₁ k)).out
    rw [LeftCosetSpace.out_mk_of_invariant _ f hleft]
    let g := map F (fam.M fam.top) G (fam.l fam.top ≫ fam.p fam.top)
      (q.out : normOneSubgroup F (fam.M fam.top)).val * k.val
    have hg : (normOnePointsIso e q.out * k₁ k).val = g := by
      change map F (fam.M fam.top) G e.hom (q.out : normOneSubgroup F (fam.M fam.top)).val *
        k.val = _
      rw [he]
    have heq : fam.squareIntegrablePairingIntegrand K fam.top x φ Φ (k, q) =
        φ (a * g) * starRingEnd ℂ (Φ (a * g)) := by
      simp only [squareIntegrablePairingIntegrand, a, g, mul_assoc]
    rw [heq, hφcentre _ ha, hν _ ha, map_mul]
    dsimp only [f, shiftFactor]
    rw [hg]
    ring
  have hinner (k : K) :
      (∫ q, fam.squareIntegrablePairingIntegrand K fam.top x φ Φ (k, q)
        ∂(normOneRationalQuotientHaarMeasure F (fam.M fam.top))) = 0 := by
    simp_rw [hSection, integral_const_mul]
    rw [← integral_map_equiv qIso (fun q => b (r k q)), hmeasure, integral_smul_measure]
    have hr := measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F G (k₁ k)
    have hrZero : (∫ q, b (r k q) ∂(normOneRationalQuotientHaarMeasure F G)) = 0 :=
      (hr.integral_comp (r k).measurableEmbedding b).trans hzero
    rw [hrZero, smul_zero, mul_zero]
  rw [squareIntegrablePairingMeasure, integral_prod _ hInt]
  simp_rw [hinner]
  simp

end StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- The full standard parabolic case of weak constant term orthogonality reduces to the
absolute convergence of the unitary component integrals. The zero integral follows directly
from a split-centre wave packet. -/
def WavePacketWeakConstantTermTopOrthogonalityReductionStatement : Prop :=
  WeakConstantTermComponentPairingIntegrableStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (fam : StandardParabolicFamily F G) (hK : IsIwasawaCompact (fam.p fam.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    (∀ Θ, IsWavePacket F G K rho hsmooth hcalc Θ →
      ∫ q : RationalQuotient F G, Φ q.out * starRingEnd ℂ (Θ q.out)
        ∂(rationalQuotientHaarMeasure F G) = 0) →
    ∀ ψ, fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top Φ ψ →
      fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc fam.top ψ

theorem wavePacketWeakConstantTermTopOrthogonalityReduction :
    WavePacketWeakConstantTermTopOrthogonalityReductionStatement := by
  classical
  intro hconv F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho fam hK Φ hΦ horth ψ hψ
    φ hφ x hx
  have hψΦ : ψ = Φ := hψ.unique (fam.isWeakConstantTerm_top hΦ)
  have hInt : Integrable (fam.squareIntegrablePairingIntegrand K fam.top x φ ψ)
      (fam.squareIntegrablePairingMeasure K hK.isCompact fam.top) := by
    obtain ⟨s, c, hsc, hs⟩ := hψ
    let u := s.filter (fun lam => parameterRealPart F (fam.P fam.top) lam = 0)
    have hint := integrable_finsetSum u (f := fun lam =>
      fam.squareIntegrablePairingIntegrand K fam.top x φ (c lam)) (fun lam hlam =>
        hconv F G hG K rho hsmooth hcalc hKmax hrho fam hK Φ hΦ fam.top s c hsc lam
          (Finset.mem_filter.mp hlam).1 (Finset.mem_filter.mp hlam).2 φ hφ x hx)
    apply hint.congr
    exact Filter.Eventually.of_forall fun z => by
      simp [hs, StandardParabolicFamily.unitaryExponentSum, u,
        StandardParabolicFamily.squareIntegrablePairingIntegrand, map_sum, Finset.mul_sum]
  refine ⟨hInt, ?_⟩
  rw [hψΦ] at hInt ⊢
  obtain ⟨ν, hν⟩ := hΦ.2.1
  have hzero := fam.normOnePairing_top_eq_zero hK hφ hΦ.1.1 ν hν horth
  exact fam.topPairingIntegral_eq_zero_of_normOne hK hφ hΦ.1.1 ν hν x hx hInt hzero

end Langlands.Global
