import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation
import Langlands.Automorphic.GroupSchemeArchimedeanHarishChandraFiniteness
import Langlands.Automorphic.GroupSchemeArithmeticSliceExtension
import Langlands.Automorphic.GroupSchemeAdelicSliceGrowth
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthProof
import Langlands.Global.RepresentationGrowthIndependence

/-! # Arithmetic Harish-Chandra finiteness from adelic rational finiteness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.RepresentationGrowth Langlands.GroupScheme
  AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

private theorem polynomialGrowth_of_infiniteAdelicHeight {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 ≤ r ∧ ∀ x,
      ‖f x‖ ≤ C * adelicHeightAtLeastOne rho (ofInfinite F G x) ^ r) :
    RepresentationGrowth.HasPolynomialGrowth F G rho f := by
  obtain ⟨C, hC, r, _, hf⟩ := hf
  obtain ⟨n, hn⟩ := exists_nat_ge r
  let s := ∑ v : NumberField.InfinitePlace F, v.mult
  let B := max 1 (AdelicMatrixHeight.sliceHeightConstant F N (finiteMatrix F G rho 1))
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C * B ^ n, mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hB) _), s * n,
    fun x => ?_⟩
  let H := adelicHeightAtLeastOne rho (ofInfinite F G x)
  have hH : 1 ≤ H := le_max_left _ _
  have hHx : H ≤ B * height F G rho x ^ s := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ (one_le_height F G rho x))
    · rw [ofInfinite_eq_pair]
      exact (adelicHeight_pair_le F G rho x 1).trans <|
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (height_nonneg F G rho x) _)
  calc
    ‖f x‖ ≤ C * H ^ r := hf x
    _ ≤ C * H ^ n := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hH hn
    _ ≤ C * (B * height F G rho x ^ s) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hH) hHx n) hC.le
    _ = C * B ^ n * height F G rho x ^ (s * n) := by rw [mul_pow, pow_mul, mul_assoc]

omit [IsAffine G.X.left] in
private theorem infiniteHeight_leftTranslate {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    {f : InfiniteAdelicGroupPoints F G → ℂ} (hf : RepresentationGrowth.HasPolynomialGrowth F G rho f)
    (a : InfiniteAdelicGroupPoints F G) :
    RepresentationGrowth.HasPolynomialGrowth F G rho (fun x => f (a * x)) := by
  obtain ⟨C, hC, n, hf⟩ := hf
  refine ⟨C * height F G rho a ^ n, mul_nonneg hC (pow_nonneg (height_nonneg F G rho a) _), n,
    fun x => (hf _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (height_nonneg F G rho _) (height_mul_le F G rho a x) n) hC

/-- Fixed-data finiteness on the rational adelic quotient implies fixed-data finiteness
on the actual archimedean arithmetic quotients. -/
def ArithmeticHarishChandraFinitenessReductionStatement : Prop :=
  RationalHarishChandraFinitenessStatement.{u} → ArithmeticHarishChandraFinitenessStatement.{u}

/-- Extend from the single finite double coset and restrict back to its chosen slice. -/
theorem arithmeticHarishChandraFiniteness_of_rational :
    ArithmeticHarishChandraFinitenessReductionStatement.{u} := by
  classical
  intro hRat F _ _ G _ hG N d rho _hrho hsmooth hcalc L _hL b H hH J hJ E hE
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨m, sigma, hSigma⟩ := Langlands.Plancherel.exists_isClosedSubgroup_fin_succ G
  let S := Submodule.span ℂ {f : AdelicGroupPoints F G → ℂ |
    IsLeftInvariantUnder F G (rationalSubgroup F G) f ∧ IsAdelicSmoothFunction F G f ∧
    HasModerateGrowthFunction F G sigma f ∧
    (∀ c ∈ L, ∀ g, f (g * ofFinite F G c) = f g) ∧
    (∀ z ∈ J, ∀ c : FiniteAdelicGroupPoints F G,
      ∀ hf : functionInfiniteSlice F G f c ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G f c, hf⟩ = 0) ∧
    ∀ g, (fun k : H => f (g * ofInfinite F G k)) ∈ E}
  let : FiniteDimensional ℂ S := hRat F G hG sigma hSigma hsmooth hcalc L H hH J hJ E hE
  let R : S →ₗ[ℂ] (InfiniteAdelicGroupPoints F G → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun x => pair F G x b)).comp S.subtype
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range R) (Submodule.span_le.mpr ?_)
  rintro f ⟨hInv, hGrowth, ⟨hf, hAnn⟩, hProfile⟩
  let f₀ : InfinitePlotSmoothFunctions F G := ⟨f, hf⟩
  have hArith : f₀ ∈ arithmeticSliceFunctions F G L b := by
    apply (mem_arithmeticSliceFunctions F G L b f₀).mpr
    intro q hq x
    apply hInv _ ⟨q, ?_, rfl⟩ x
    change b⁻¹ * finite F G (rational F G q) * (b⁻¹)⁻¹ ∈ L.toSubgroup
    rw [inv_inv]
    exact hq
  let F₁ := extendArithmeticPlotSmooth F G L b hsmooth ⟨f₀, hArith⟩
  let f₁ := evaluate F G F₁.val
  have hLevel (c : L) (g : AdelicGroupPoints F G) : f₁ (g * ofFinite F G c.val) = f₁ g :=
    evaluate_extendArithmeticPlotSmooth_mul_ofFinite F G L b hsmooth ⟨f₀, hArith⟩ c g
  have hSlice (c : FiniteAdelicGroupPoints F G) :
      finitePlotSmoothSlice F G c F₁ = 0 ∨ ∃ a : InfiniteAdelicGroupPoints F G,
        finitePlotSmoothSlice F G c F₁ = plotSmoothLeftTranslation F G a f₀ :=
    finitePlotSmoothSlice_extendArithmeticPlotSmooth_eq_zero_or F G L b hsmooth ⟨f₀, hArith⟩ c
  have hSliceVal (c : FiniteAdelicGroupPoints F G) :
      (finitePlotSmoothSlice F G c F₁).val = functionInfiniteSlice F G f₁ c := rfl
  have hS : f₁ ∈ S := by
    apply Submodule.subset_span
    refine ⟨?_, ?_, ?_, fun c hc => hLevel ⟨c, hc⟩, ?_, ?_⟩
    · rintro _ ⟨q, rfl⟩ g
      exact evaluate_rational_mul F G F₁.val q g
    · exact ⟨F₁.val.property, fun c => (hSliceVal c) ▸ (finitePlotSmoothSlice F G c F₁).property,
        L.toSubgroup, L.isOpen, fun c hc => hLevel ⟨c, hc⟩⟩
    · have hg₀ := RepresentationGrowth.HasPolynomialGrowth.of_closedImmersion F G sigma rho hSigma
        (polynomialGrowth_of_infiniteAdelicHeight rho hGrowth)
      refine adelicSliceModerateGrowthStatement F G sigma hG hSigma (Nat.succ_pos _) F₁.val
        F₁.property.2 (fun c => ?_)
      change RepresentationGrowth.HasPolynomialGrowth F G sigma (finitePlotSmoothSlice F G c F₁).val
      rcases hSlice c with hzero | ⟨a, ha⟩
      · rw [hzero]
        exact RepresentationGrowth.HasPolynomialGrowth.zero
      · rw [ha]
        exact infiniteHeight_leftTranslate sigma hg₀ a
    · intro z hz c hc
      change plotSmoothCenterAction F G hsmooth hcalc z (finitePlotSmoothSlice F G c F₁) = 0
      rcases hSlice c with hzero | ⟨a, ha⟩
      · rw [hzero, map_zero]
      · rw [ha]
        change plotSmoothEnvelopingAction F G hsmooth hcalc z.val
          (plotSmoothLeftTranslation F G a f₀) = 0
        rw [plotSmoothEnvelopingAction_leftTranslation hcalc, show plotSmoothEnvelopingAction F G hsmooth
          hcalc z.val f₀ = 0 from hAnn z hz, map_zero]
    · intro g
      rw [← pair_projections F G g]
      have heq : (fun k : H => f₁ (pair F G (infinite F G g) (finite F G g) * ofInfinite F G k)) =
          fun k : H => (finitePlotSmoothSlice F G (finite F G g) F₁).val
            (infinite F G g * k.val) := by
        funext k
        rw [ofInfinite_eq_pair, pair_mul, mul_one, finitePlotSmoothSlice_apply]
      rw [heq]
      rcases hSlice (finite F G g) with hzero | ⟨a, ha⟩
      · rw [hzero]
        exact E.zero_mem
      · rw [ha]
        simpa only [plotSmoothLeftTranslation_apply, ← mul_assoc] using hProfile (a * infinite F G g)
  refine ⟨⟨f₁, hS⟩, ?_⟩
  funext x
  change (finitePlotSmoothSlice F G b F₁).val x = f x
  rw [finitePlotSmoothSlice_extendArithmeticPlotSmooth]

end Langlands.Automorphic.GroupSchemeFunctions
