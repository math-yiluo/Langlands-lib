import Langlands.Global.AdelicAmbientWavePacketProfileFourier
import Langlands.Global.AdelicWavePacketUnitaryCentrePairing
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicRelativeWavePacketDescentStatement
import Langlands.Global.AdelicSpectralBump
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Relative wave-packet tests of an automorphic form with a unitary central character -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
open RestrictionSplitCentre (canonicalRationalSubgroup canonicalSubgroup positiveCentreHaarMeasure)

private theorem integrable_wavePacket_pairing_of_logL2
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] {N m : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (Θ Φ : AdelicGroupPoints F G → ℂ)
    (hΘ : MemLp (fun q : RationalQuotient F G => Θ q.out * (rationalLogHeight F G rho q : ℂ) ^ m)
      2 (rationalQuotientHaarMeasure F G))
    (hΦ : MemLp (fun q : RationalQuotient F G => Φ q.out / (rationalLogHeight F G rho q : ℂ) ^ m)
      2 (rationalQuotientHaarMeasure F G)) :
    Integrable (fun q : RationalQuotient F G => Θ q.out * starRingEnd ℂ (Φ q.out))
      (rationalQuotientHaarMeasure F G) := by
  have hprod := hΘ.integrable_mul hΦ.star
  apply hprod.congr
  filter_upwards with q
  have hheight : (rationalLogHeight F G rho q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_pos.trans_le (one_le_rationalLogHeight rho q)).ne'
  change (Θ q.out * (rationalLogHeight F G rho q : ℂ) ^ m) *
      starRingEnd ℂ (Φ q.out / (rationalLogHeight F G rho q : ℂ) ^ m) = _
  rw [map_div₀, map_pow, Complex.conj_ofReal]
  field_simp

private theorem relativePairing_of_lifts
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Φ Θ : AdelicGroupPoints F G → ℂ)
    (hΦ : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ)
    (hΘ : IsLeftInvariantUnder F G (canonicalRationalSubgroup F G) Θ)
    (horth : ∀ Ψ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Ψ →
      ∫ q : RationalQuotient F G, Φ q.out * starRingEnd ℂ (Ψ q.out)
        ∂(rationalQuotientHaarMeasure F G) = 0)
    (hdecay : ∀ Ψ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Ψ →
      ∀ m : ℕ, MemLp (fun q : RationalQuotient F G =>
        Ψ q.out * (rationalLogHeight F G rho q : ℂ) ^ m) 2 (rationalQuotientHaarMeasure F G))
    (hlift : ∀ {m : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G)
      (b : (Fin m → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
      IsWavePacket F G K rho hsmooth hcalc (fun g => ambientWavePacketProfile e b g * Θ g)) :
    let relativePairing (q : NormOneRationalQuotient F G) :=
      Θ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
    Integrable relativePairing (normOneRationalQuotientHaarMeasure F G) ∧
      ∫ q, relativePairing q ∂(normOneRationalQuotientHaarMeasure F G) = 0 := by
  obtain ⟨hΦaut, ⟨ν, hν⟩, logPower, hLog⟩ := hΦ
  let dimension := Module.finrank ℝ (RealCharacterParameter F G)
  let e := ambientParameterChart hG
  let translation := Homeomorph.addRight (-(e.symm ν))
  let β := spectralBump dimension
  let b := β.val ∘ translation
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := β.property.1.comp (contDiff_id.add contDiff_const)
  have hbc : HasCompactSupport b := β.property.2.1.comp_homeomorph translation
  have hbone : b (e.symm ν) = 1 := by
    change β.val (e.symm ν + -(e.symm ν)) = 1
    rw [add_neg_cancel]
    exact β.property.2.2
  obtain ⟨c, hc, hinv⟩ := ambientWavePacketProfileFourierInversion F G hG e
  obtain ⟨_, hcValue⟩ := hinv b hb hbc ν
  have hnonzero : (∫ a : canonicalSubgroup F G,
      ambientWavePacketProfile e b a.val *
        starRingEnd ℂ (parameterPower F G (imaginaryParameter F G ν) a.val)
      ∂(positiveCentreHaarMeasure F G hG)) ≠ 0 := by
    rw [hcValue, hbone, mul_one]
    exact Complex.ofReal_ne_zero.mpr hc.ne'
  let Ψ : AdelicGroupPoints F G → ℂ := fun g => ambientWavePacketProfile e b g * Θ g
  have hΨ : IsWavePacket F G K rho hsmooth hcalc Ψ := hlift e b hb hbc
  have hfullInt := integrable_wavePacket_pairing_of_logL2 rho Ψ Φ (hdecay Ψ hΨ logPower) hLog
  have hfullZero : (∫ q : RationalQuotient F G, Ψ q.out * starRingEnd ℂ (Φ q.out)
      ∂(rationalQuotientHaarMeasure F G)) = 0 := by
    have hconj := congrArg (starRingEnd ℂ) (horth Ψ hΨ)
    rw [map_zero, ← integral_conj] at hconj
    simpa only [map_mul, starRingEnd_apply, star_star, mul_comm] using hconj
  have ⟨hInt, hEq⟩ :=
    wavePacketUnitaryCentrePairing F G hG e b ν Θ Φ hΦaut.1 hν hΘ hnonzero
  exact ⟨hInt.mp hfullInt, (mul_eq_zero.mp (hEq.symm.trans hfullZero)).resolve_left hnonzero⟩

/-- If a logarithmically weighted automorphic form with a unitary central character is
orthogonal to all full packets, its pairing with a relative packet on the norm-one
quotient is absolutely integrable and zero. -/
def RelativeWavePacketTestedFormStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (iU : U ⟶ P) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
      (_ : IsClosedImmersion p₀.hom.hom.left),
      IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ (Φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    (∀ Ψ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Ψ →
      ∫ q : RationalQuotient F G, Φ q.out * starRingEnd ℂ (Ψ q.out)
        ∂(rationalQuotientHaarMeasure F G) = 0) →
    ∀ (Θ : AdelicGroupPoints F G → ℂ),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
    let relativePairing (q : NormOneRationalQuotient F G) :=
      Θ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
    Integrable relativePairing (normOneRationalQuotientHaarMeasure F G) ∧
      ∫ q, relativePairing q ∂(normOneRationalQuotientHaarMeasure F G) = 0

/-- The ambient lift, descent, and opposite logarithmic weights give the norm-one
quotient tests appearing in Delorme's proof of Theorem 7.9. -/
theorem relativeWavePacketTestedForm_of_lift_descent_decay
    (hLift : WavePacketAmbientLiftStatement) (hDescent : RelativeWavePacketDescentStatement)
    (hDecay : WavePacketRapidDecayStatement) : RelativeWavePacketTestedFormStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho
    hsmooth hcalc hKmax hrho hMin Φ hΦ horth Θ
  let _ := IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  intro hΘ
  exact relativePairing_of_lifts hG K rho hsmooth hcalc Φ Θ hΦ
    (hDescent F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc Θ hΘ).1 horth
    (hDecay F G hG K rho hsmooth hcalc hKmax hrho hMin) fun e b hb hbc =>
      hLift F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc e b hb hbc Θ hΘ

end Langlands.Global
