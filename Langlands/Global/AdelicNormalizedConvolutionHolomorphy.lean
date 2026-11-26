import Langlands.Analysis.Meromorphic.FiniteDimensionalValues
import Langlands.Analysis.Meromorphic.PointwiseValues
import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction
import Langlands.Global.AdelicNormalizedConvolutionFiniteSpan
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice

/-! # Entire coefficients from finite span on the imaginary axis -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Analysis.Meromorphic
  Langlands.Analysis.SeveralComplex

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "Ad" => AdelicGroupPoints F G
local notation "Λ" => ComplexCharacterParameter F P
local notation "dh" => (Measure.haar : Measure Ad)
local notation "conv" => fun kernel v lam g => ∫ h, kernel h * hK.inducedRightTranslate lam h v g ∂dh

/-- Evaluating the normalized convolution at an adelic point gives an entire function of the
complex parameter. Compact support of the kernel bounds the integrand uniformly on compact
parameter sets. -/
theorem IsIwasawaCompact.differentiable_integral_translate
    {kernel v : Ad → ℂ} (hk : Continuous kernel) (hks : HasCompactSupport kernel)
    (hv : Continuous v) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] Λ) (g : Ad) :
    Differentiable ℂ (fun s => conv kernel v (e s) g) := by
  let integrand (s : Fin n → ℂ) (h : Ad) := kernel h * hK.inducedRightTranslate (e s) h v g
  let heightDiff (h : Ad) := hK.height (g * h) - hK.height g
  have hformula (s : Fin n → ℂ) (h : Ad) :
      integrand s h = (kernel h * v (g * h)) *
        Complex.exp (complexParameterPairing F P (e s) (heightDiff h)) := by
    simp only [integrand, IsIwasawaCompact.inducedRightTranslate, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower, heightDiff, map_neg, LinearMap.neg_apply, map_add,
      sub_eq_add_neg, Complex.exp_add]
    ring
  have hcont : Continuous (Function.uncurry integrand) := by
    have hH : Continuous heightDiff := (hK.continuous_height.comp (continuous_const.mul continuous_id)).sub
      continuous_const
    change Continuous (fun z : (Fin n → ℂ) × Ad => integrand z.1 z.2)
    simp_rw [hformula]
    exact ((hk.comp continuous_snd).mul (hv.comp (continuous_const.mul continuous_snd))).mul
      (Complex.continuous_exp.comp ((continuous_complexParameterPairing_coordinates e.toLinearMap).comp
        (continuous_fst.prodMk (hH.comp continuous_snd))))
  have hDiff (h : Ad) : Differentiable ℂ (fun s => integrand s h) := by
    let paired : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun s => complexParameterPairing F P (e s) (heightDiff h)
        map_add' := fun s t => by simp only [map_add, LinearMap.add_apply]
        map_smul' := fun a s => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
    simp_rw [hformula]
    exact (differentiable_const _).mul paired.toContinuousLinearMap.differentiable.cexp
  let S := tsupport kernel
  let ν := Measure.restrict dh S
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (hks.isCompact.measure_lt_top («μ» := dh)).ne
  rw [← differentiableOn_univ]
  have hzero (s : Fin n → ℂ) (h : Ad) (hh : h ∉ S) : integrand s h = 0 := by
    change kernel h * hK.inducedRightTranslate (e s) h v g = 0
    rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
  have hEq : (fun s => conv kernel v (e s) g) = fun s => ∫ h, integrand s h ∂ν := by
    funext s
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero s)).symm
  rw [hEq]
  refine differentiableOn_integral_of_bounded ν integrand isOpen_univ
    (fun h => (hDiff h).differentiableOn) (fun s _ => ?_) ?_
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  intro C _ hC
  obtain ⟨B, hB⟩ := (hC.prod hks.isCompact).bddAbove_image hcont.norm.continuousOn
  refine ⟨max B 0, fun s hs h => ?_⟩
  by_cases hh : h ∈ S
  · exact (hB ⟨(s, h), ⟨hs, hh⟩, rfl⟩).trans (le_max_left _ _)
  · rw [hzero s h hh, norm_zero]
    exact le_max_right _ _

/-- If the imaginary-axis convolutions lie in the span of a fixed finite family of functions
with property `Pr`, the convolution on the whole complex parameter space has an entire finite
expansion by forms with the same property. -/
theorem IsIwasawaCompact.exists_finiteNormalizedConvolutionExpansion_of_span_imaginary
    {kernel v : Ad → ℂ} (hk : Continuous kernel) (hks : HasCompactSupport kernel)
    (hv : Continuous v) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (Pr : (Ad → ℂ) → Prop) {m : ℕ} (u : Fin m → Ad → ℂ) (hu : ∀ j, Pr (u j))
    (hSpan : ∀ x : RealCharacterParameter F P,
      conv kernel v (imaginaryParameter F P x) ∈ Submodule.span ℂ (range u)) :
    ∃ (m' : ℕ) (w : Fin m' → Ad → ℂ) (b : Fin m' → Λ → ℂ),
      (∀ j, Pr (w j)) ∧ IsFiniteNormalizedConvolutionExpansion hK kernel v w b := by
  let e₀ := realChart e
  let : FiniteDimensional ℂ Λ :=
    FiniteDimensional.of_injective e₀.symm.toLinearMap e₀.symm.injective
  have hDiff (k : ℕ) (e' : (Fin k → ℂ) ≃ₗ[ℂ] Λ) (g : Ad) :
      Differentiable ℂ (fun s => conv kernel v (e' s) g) :=
    hK.differentiable_integral_translate hk hks hv e' g
  have hM : IsMeromorphicInCoordinatesOn (conv kernel v) univ := by
    refine ⟨inferInstance, fun k e' => ?_⟩
    rw [preimage_univ]
    have hhol : IsHolomorphicOn 𝓘(ℂ, Fin k → ℂ) ((conv kernel v) ∘ e') univ :=
      isHolomorphicOn_pi_of_differentiableOn (fun g => (hDiff k e' g).differentiableOn)
    exact ⟨isOpen_univ, dense_univ, hhol, fun s =>
      ⟨univ, isOpen_univ, isConnected_univ, mem_univ s, fun _ => 1, (conv kernel v) ∘ e',
        mdifferentiableOn_const, ⟨s, mem_univ s, one_ne_zero⟩, hhol, fun t _ => one_smul ℂ _⟩⟩
  have hex := exists_meromorphic_expansion_of_mem_span Pr u hu hM
    (S := range (imaginaryParameter F P)) (by rintro _ ⟨x, rfl⟩; exact hSpan x)
  obtain ⟨m', w, b, hw, hb, hEq⟩ := hex
  refine ⟨m', w, b, hw, hb, fun lam g => ?_⟩
  let f (s : Fin n → ℂ) := conv kernel v (e₀ s) g - ∑ j, b j (e₀ s) * w j g
  have hbDiff (j : Fin m') : DifferentiableOn ℂ (fun s => b j (e₀ s)) univ := by
    have h := ((hb j).2 n e₀).2.2.1
    rw [preimage_univ] at h
    exact differentiableOn_of_isHolomorphicOn h
  have hF : DifferentiableOn ℂ f univ := (hDiff n e₀ g).differentiableOn.sub
    (DifferentiableOn.fun_sum fun j _ => (hbDiff j).mul_const (w j g))
  have hIm (s : Fin n → ℂ) (hs : ∀ j, (s j).re = 0) : f s = 0 := by
    obtain ⟨x, hx⟩ := realChart_mem_range_imaginary e s hs
    exact sub_eq_zero.mpr (hEq (e₀ s) ⟨x, hx.symm⟩ g)
  have hBall := ImaginaryHyperplane.eqOn_zero_of_eqOn_imaginary (s₀ := 0) (δ := 1)
    (fun _ => Complex.zero_re) (hF.mono (subset_univ _)) (fun s _ hs => hIm s hs)
  have hGlob := differentiableOn_eqOn_zero_of_isPreconnected hF isOpen_univ isPreconnected_univ
    Metric.isOpen_ball (subset_univ _) (Metric.nonempty_ball.mpr zero_lt_one) hBall
  have h := sub_eq_zero.mp (hGlob (mem_univ (e₀.symm lam)))
  change conv kernel v (e₀ (e₀.symm lam)) g = ∑ j, b j (e₀ (e₀.symm lam)) * w j g at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- With the Iwasawa data and compatible Haar measure for a presented parabolic, the
normalized convolutions at imaginary parameters lie in the span of a fixed finite family
of square-integrable inducing forms. -/
def NormalizedConvolutionImaginarySpanStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsIso (subgroupMultiplication l iU) → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ v : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v →
    ∀ kernel : AdelicGroupPoints F G → ℂ,
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) kernel →
      ∃ (m : ℕ) (u : Fin m → AdelicGroupPoints F G → ℂ),
        (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (u j)) ∧
        ∀ x : RealCharacterParameter F P,
          (fun g => ∫ h, kernel h * hK.inducedRightTranslate (imaginaryParameter F P x) h v g
            ∂(Measure.haar : Measure (AdelicGroupPoints F G))) ∈ Submodule.span ℂ (range u)

set_option synthInstance.maxHeartbeats 200000 in
/-- Finite square-integrable span on the imaginary axis is sufficient for a finite entire
expansion of the normalized convolutions. -/
theorem normalizedConvolutionFiniteSpan_of_imaginarySpan
    (hspan : NormalizedConvolutionImaginarySpanStatement) :
    NormalizedConvolutionFiniteSpanStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU hmul hπ K hK N d
    rho hsmooth hcalc hmax hrho μM _ hμM v hv kernel hk
  let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p)
    (inferInstance : IsClosedImmersion p.hom.hom.left)
  have := (r.rationalCharacters_free_finite hG).2
  let : FiniteDimensional ℝ (RealCharacterParameter F P) := Module.Finite.base_change ℤ ℝ _
  let n := Module.finrank ℝ (RealCharacterParameter F P)
  let e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P :=
    (Module.finBasis ℝ (RealCharacterParameter F P)).equivFun.symm
  have hex := hspan F G P M U A p iU l a r hA hT π hG hU hmul hπ K hK rho hsmooth hcalc hmax hrho
    μM hμM v hv kernel hk
  obtain ⟨m, u, hu, hIm⟩ := hex
  exact hK.exists_finiteNormalizedConvolutionExpansion_of_span_imaginary hk.1 hk.2.1 hv.1.2.1.1 e
    (IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l) u hu hIm

end Langlands.Global
