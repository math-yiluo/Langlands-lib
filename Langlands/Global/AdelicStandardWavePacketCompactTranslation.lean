import Langlands.Global.AdelicNonAssociateWavePacketOrthogonality
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicSquareIntegrableHeightConjugateCompact

/-! # Infinite compact conjugation of standard-parabolic wave packets -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  [IsClosedImmersion (fam.p J).hom.hom.left]
  (r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus (fam.A J).toGrp) (hT : IsSplitTorus r.data.T.toGrp)

local notation "Gₐ" => AdelicGroupPoints F G
local notation "P" => fam.P J

/-- A translated standard-parabolic packet integrand has a one-form presentation at the
conjugate compact, with the original spectral coordinates and continuation domain. -/
def StandardWavePacketCompactTranslationStatement : Prop :=
  ∀ {K : Subgroup Gₐ} (hK : IsIwasawaCompact (fam.p J) K)
    (a : InfiniteAdelicGroupPoints F G),
  let t := ofInfinite F G a
  let L := K.map (MulAut.conj t).toMonoidHom
  ∀ (hL : IsIwasawaCompact (fam.p J) L)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
    {φ : Gₐ → ℂ},
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ →
  ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (c : (Fin n → ℝ) → ℂ) (E : ComplexCharacterParameter F P → Gₐ → ℂ)
    (D : Set (ComplexCharacterParameter F P)),
    ContDiff ℝ (⊤ : ℕ∞) c → HasCompactSupport c →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
  let φ' : Gₐ → ℂ := fun g => φ (g * t)
  IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ' ∧
  ∃ (c' : (Fin n → ℝ) → ℂ) (E' : ComplexCharacterParameter F P → Gₐ → ℂ),
    ContDiff ℝ (⊤ : ℕ∞) c' ∧ HasCompactSupport c' ∧
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D) ∧
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E' lam = hL.eisensteinSeries φ' lam) ∧
    ∀ x g, c' x * E' (imaginaryParameter F P (e x)) g = c x * E (imaginaryParameter F P (e x)) (g * t)

/-- The height at the inverse translating point supplies an entire scalar factor. Its inverse
is absorbed into the smooth spectral test. -/
theorem standardWavePacketCompactTranslation :
    fam.StandardWavePacketCompactTranslationStatement J r hA hT := by
  intro K hK a t L hL N d rho hsmooth hcalc φ hφ n e c E D hc hcpt hE hreg φ'
  have hφ' : IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) φ' :=
    fam.isSquareIntegrableInducedForm_infiniteRightTranslate J rho hsmooth hcalc hK a hL.isCompact hφ
  obtain ⟨q, b, hb, ht⟩ := hL.exists_eq t⁻¹
  have hscalar (lam : ComplexCharacterParameter F P) :
      hL.heightPower lam t⁻¹ = parameterPower F P lam q := by
    rw [IsIwasawaCompact.heightPower, hL.height_eq hb ht, parameterPower]
  let ℓ : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
    (((complexParameterPairing F P).flip (characterLog F P q)).restrictScalars ℝ).comp
      ((imaginaryParameter F P).comp e.toLinearMap)
  let c' (x : Fin n → ℝ) := c x * Complex.exp (-ℓ x)
  let E' (lam : ComplexCharacterParameter F P) (g : Gₐ) :=
    parameterPower F P lam q * E lam (g * t)
  refine ⟨hφ', c', E', hc.mul ℓ.toContinuousLinearMap.contDiff.neg.cexp, hcpt.mul_right, ?_, ?_, ?_⟩
  · intro g
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE (g * t)).1
    simpa only [Set.univ_inter, E', Pi.mul_def] using
      (isMeromorphicInCoordinatesOn_parameterPower q).mul (hE (g * t))
  · obtain ⟨R, hR⟩ := hreg
    refine ⟨R, fun lam hlam => ?_⟩
    funext g
    have hV : (fun x => φ' (x * t⁻¹)) = φ := by
      funext x
      simp only [φ', inv_mul_cancel_right]
    have he : ∀ (hL' : IsIwasawaCompact (fam.p J) (K.map (MulAut.conj t).toMonoidHom)),
        hL'.eisensteinSeries φ' lam g = hL'.heightPower lam t⁻¹ * hK.eisensteinSeries φ lam (g * t) := by
      simpa only [inv_inv, mul_inv_cancel_right, hV] using
        (fun hL' => hK.eisensteinSeries_mul_conjInv t⁻¹ hL' φ' lam (g * t))
    change parameterPower F P lam q * E lam (g * t) = _
    rw [hR lam hlam, ← hscalar]
    exact (he hL).symm
  · intro x g
    have hcancel : Complex.exp (-ℓ x) * parameterPower F P (imaginaryParameter F P (e x)) q = 1 := by
      change Complex.exp (-ℓ x) * Complex.exp (ℓ x) = 1
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    change c x * Complex.exp (-ℓ x) *
      (parameterPower F P (imaginaryParameter F P (e x)) q * E (imaginaryParameter F P (e x)) (g * t)) = _
    rw [mul_assoc (c x), ← mul_assoc (Complex.exp (-ℓ x)), hcancel, one_mul]

/-- Right translation preserves the standard-parabolic packet presentation under conjugation
of the compact by the translating point. -/
theorem IsParabolicWavePacket.infiniteRightTranslate
    {K : Subgroup Gₐ} (hK : IsIwasawaCompact (fam.p J) K)
    (a : InfiniteAdelicGroupPoints F G)
    (hL : IsIwasawaCompact (fam.p J) (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom))
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
    {Θ : Gₐ → ℂ}
    (hΘ : IsParabolicWavePacket hK rho hsmooth hcalc (fam.iU J) (fam.l J) r hA hT Θ) :
    IsParabolicWavePacket hL rho hsmooth hcalc (fam.iU J) (fam.l J) r hA hT
      (fun g => Θ (g * ofInfinite F G a)) := by
  obtain ⟨n, e, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘeq⟩ := hΘ
  have h (j : Fin k) := fam.standardWavePacketCompactTranslation J r hA hT hK a hL
    (hv j) e (c j) (E j) D (hc j).1 (hc j).2 (hE j) (hreg j)
  choose hj c' E' hc' hcpt' hE' hreg' heq using h
  refine ⟨n, e, k, fun j g => v j (g * ofInfinite F G a), c', E', D, hj,
    fun j => ⟨hc' j, hcpt' j⟩, hD, hE', hreg', ?_⟩
  rw [hΘeq]
  funext g
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    Finset.sum_congr rfl fun j _ => (heq j x g).symm)

end Langlands.Global.StandardParabolicFamily
