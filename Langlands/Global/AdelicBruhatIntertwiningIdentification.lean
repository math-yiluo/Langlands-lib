import Langlands.Global.AdelicEisensteinBruhatAbsoluteBound

/-! # The absolutely convergent intertwining integral for a Bruhat piece -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine V.X.left] [IsAffine P'.X.left] [IsAffine U'.X.left]
  [IsAffine V'.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')
  [IsClosedImmersion (f ≫ p).hom.hom.left] [IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left]
  [IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (hK' : IsIwasawaCompact (f ≫ p) K)

local notation "Points" => AdelicGroupPoints F G
local notation "wₐ" => innerAdelicPoint F G w
local notation "j" => (iV ≫ q)
local notation "jU" => (iU' ≫ f ≫ p)
local notation "jV" => (iV' ≫ g' ≫ q)
local notation "μ" => stabilizerMeasure F p j wₐ
local notation "μ'" => intertwiningMeasure F (f ≫ p) iU' jV wₐ
local notation "twist" => hK.parameterTwist
local notation "S" => eisensteinStabilizerIntegrand p q iV wₐ

omit [IsAffineHom G.X.hom] [IsAffine V.X.left] [IsAffine V'.X.left]
  [IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left] in
/-- The twist on the smaller source constant term uses restriction of
the original parameter. -/
theorem intertwiningIntegrand_eq_twistedConstantTerm (hU' : IsUnipotent U')
    (φ : Points → ℂ) (lam : ComplexCharacterParameter F P) (y : Points) :
    hK'.intertwiningIntegrand iU' jV w (subgroupConstantTerm F jU φ)
        (parameterRestrict f lam) y =
      fun x => subgroupConstantTerm F jU (twist φ lam)
        (wₐ⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range jV)).val * y) := by
  funext x
  have hm : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range jU), ∀ z,
      hK.heightPower lam (u * z) = hK.heightPower lam z := by
    rintro _ ⟨u, rfl⟩ z
    have h := hK.heightPower_unipotent_mul hU' (iU' ≫ f) lam u z
    rwa [Category.assoc] at h
  simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist]
  rw [hK.heightPower_restrict f hK' lam,
    show twist φ lam = fun z => φ z * hK.heightPower lam z from rfl,
    subgroupConstantTerm_mul_invariant jU φ _ hm]

/-- Under the geometric unfolding identity, absolute convergence of the
original stabilizer integral implies absolute convergence of the actual
smaller intertwiner. Their values agree and the smaller absolute integral
is bounded by the original absolute integral. -/
def BruhatIntertwiningIdentificationStatement : Prop :=
  GeometricLemmaUnfoldingStatement.{u} →
  IsConnectedReductive G → IsParabolicSubgroup p →
  LeviSubgroup.IsGeometricUnipotentRadical iU →
  IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
  IsParabolicSubgroup (f ≫ p) → LeviSubgroup.IsGeometricUnipotentRadical iU' →
  IsParabolicSubgroup (g' ≫ q) → LeviSubgroup.IsGeometricUnipotentRadical iV' →
  IsGeometricLemmaDatum p iU q iV f g' w →
  ∀ (φ : Points → ℂ) (lam : ComplexCharacterParameter F P),
    Measurable (twist φ lam) →
    IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) (twist φ lam) →
    IsLeftInvariantUnder F G (rationalImage F p) (twist φ lam) →
    ∀ y : Points, Integrable (S (twist φ lam) y) μ →
      let k := hK'.intertwiningIntegrand iU' jV w (subgroupConstantTerm F jU φ)
        (parameterRestrict f lam) y
      Integrable k μ' ∧ (∫ x, k x ∂μ') = (∫ x, S (twist φ lam) y x ∂μ) ∧
        (∫⁻ x, ‖k x‖ₑ ∂μ') ≤ ∫⁻ x, ‖S (twist φ lam) y x‖ₑ ∂μ

set_option maxHeartbeats 1800000 in
theorem bruhatIntertwiningIdentification :
    BruhatIntertwiningIdentificationStatement p iU q iV w f iU' g' iV' hK hK' := by
  intro hUnfold hG hP hU hQ hV hP' hU' hQ' hV' hDat φ lam hmeas hInvU hInvP y hRaw
  let xG := fun x : LeftCosetSpace (intertwiningRationalSubgroup F (f ≫ p) iU' jV wₐ) =>
    wₐ⁻¹ * (x.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range jV)).val * y
  let Φ₁ := fun x : Points => ((‖(twist φ lam) x‖ : ℝ) : ℂ)
  have hNorm (x : Points) : ‖Φ₁ x‖ₑ = ‖(twist φ lam) x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal (Complex.norm_of_nonneg (norm_nonneg ((twist φ lam) x)))
  have hFin : (∫⁻ x, ‖S (twist φ lam) y x‖ₑ ∂μ) < ∞ :=
    hasFiniteIntegral_iff_enorm.mp hRaw.hasFiniteIntegral
  have h := hUnfold F G P U Q V P' U' Q' V' p iU q iV w f iU' g' iV'
    hG hP hU hQ hV hP' hU' hQ' hV' hDat
  obtain ⟨hInt, hEq⟩ := h (twist φ lam) hmeas hInvU hInvP y hFin
  have hFin₁ : (∫⁻ x, ‖S Φ₁ y x‖ₑ ∂μ) < ∞ := by
    simpa only [eisensteinStabilizerIntegrand, hNorm] using hFin
  obtain ⟨hInt₁, hEq₁⟩ := h Φ₁ (Complex.continuous_ofReal.measurable.comp hmeas.norm)
    (fun x hx z => by simp only [Φ₁, hInvU x hx z])
    (fun x hx z => by simp only [Φ₁, hInvP x hx z]) y hFin₁
  dsimp only
  rw [intertwiningIntegrand_eq_twistedConstantTerm p q w f iU' g' iV' hK hK' hU'.1.isUnipotent]
  refine ⟨hInt, hEq, ?_⟩
  let k₁ := fun x => (subgroupConstantTerm F jU Φ₁ (xG x)).re
  have hk₁ (x) : k₁ x = ∫ u, ‖(twist φ lam) ((u.out : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range jU)).val * xG x)‖
      ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range jU) := by
    unfold k₁ subgroupConstantTerm
    simp only [Φ₁, integral_complex_ofReal, Complex.ofReal_re]
  have hk₀ (x) : 0 ≤ k₁ x := by rw [hk₁]; exact integral_nonneg fun _ => norm_nonneg _
  have hkInt : Integrable k₁ μ' := Complex.reCLM.integrable_comp hInt₁
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (k₁ x) ∂μ' := by
      apply lintegral_mono
      intro x
      change ‖subgroupConstantTerm F jU (twist φ lam) (xG x)‖ₑ ≤ ENNReal.ofReal (k₁ x)
      rw [← ofReal_norm, hk₁]
      apply ENNReal.ofReal_le_ofReal
      exact norm_integral_le_integral_norm _
    _ = ENNReal.ofReal (∫ x, k₁ x ∂μ') :=
      (ofReal_integral_eq_lintegral_ofReal hkInt (Filter.Eventually.of_forall hk₀)).symm
    _ = ENNReal.ofReal (∫ x, ‖S (twist φ lam) y x‖ ∂μ) := by
      congr 1
      have hRe := congrArg Complex.re hEq₁
      rw [← RCLike.re_eq_complex_re, ← integral_re hInt₁] at hRe
      simpa only [RCLike.re_eq_complex_re, k₁, xG, Φ₁, integral_complex_ofReal,
        Complex.ofReal_re, eisensteinStabilizerIntegrand] using hRe
    _ = _ := by
      rw [ofReal_integral_eq_lintegral_ofReal hRaw.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
      simp only [ofReal_norm]

end Langlands.Global
