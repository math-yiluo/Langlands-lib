import Langlands.Global.AdelicEisensteinDifferential
import Langlands.Representation.Families.FiniteHolomorphicSections
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Parameter dependence of the actual invariant derivative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

private theorem groupDirectionalValue_mul_cexp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    (X : GroupLieAlgebra I G) {f h : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℂ) ∞ h) (g : G) :
    groupDirectionalValue I X (fun z => f z * Complex.exp (h z)) g =
      (groupDirectionalValue I X f g + f g * groupDirectionalValue I X h g) *
        Complex.exp (h g) := by
  let p (z : G) := f (g * z)
  let q (z : G) := h (g * z)
  have hm : ContMDiff I I ∞ (fun z : G => g * z) := contMDiff_const.mul contMDiff_id
  have hp : MDifferentiableAt I 𝓘(ℝ, ℂ) p (1 : G) := (hf.comp hm).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt I 𝓘(ℝ, ℂ) q (1 : G) := (hh.comp hm).mdifferentiableAt (by simp)
  have he := (Complex.hasStrictFDerivAt_exp_real (q 1)).hasFDerivAt.hasMFDerivAt
  have hd := hp.hasMFDerivAt.mul (he.comp 1 hq.hasMFDerivAt)
  have hd' : mvfderiv I (p * (Complex.exp ∘ q)) 1 =
      p 1 • (Complex.exp (q 1) • (1 : ℂ →L[ℝ] ℂ)).comp (mvfderiv I q 1) +
        Complex.exp (q 1) • mvfderiv I p 1 := hd.mfderiv
  have hX := congrArg (fun D : TangentSpace I (1 : G) →L[ℝ] ℂ => D X) hd'
  change mvfderiv I (p * (Complex.exp ∘ q)) 1 X =
    (mvfderiv I p 1 X + f g * mvfderiv I q 1 X) * Complex.exp (h g)
  calc
    _ = f g * (Complex.exp (h g) * mvfderiv I q 1 X) +
        Complex.exp (h g) * mvfderiv I p 1 X := by
      simpa only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
        Function.comp_apply, p, q, mul_one, smul_eq_mul] using hX
    _ = _ := by ring

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Adeles" => AdelicGroupPoints F G
local notation "Param" => ComplexCharacterParameter F P

/-- Each scalar character pairing with the Iwasawa height is smooth in the
infinite variable at fixed finite coordinate. -/
def HasSmoothHeightPairings : Prop :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  ∀ (lam : Param) (b : FiniteAdelicGroupPoints F G),
    ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => complexParameterPairing F P lam (hK.height (pair F G a b)))

/-- Smooth untwisted slices remain smooth after the Iwasawa twist. -/
theorem contMDiff_parameterTwist_slice (hH : hK.HasSmoothHeightPairings hsmooth)
    (φ : Adeles → ℂ) (lam : Param)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => φ (pair F G a b))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => hK.parameterTwist φ lam (pair F G a b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro b
  have hexp := (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contMDiff.comp (hH lam b)
  have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_mul
  exact hmul.contMDiff.comp ((hφ b).prodMk_space hexp)

/-- The actual real invariant derivative of the height pairing is complex-linear
in the character parameter. -/
def heightPairingDirectional (hH : hK.HasSmoothHeightPairings hsmooth) (X : smoothModel F d) :
    Param →ₗ[ℂ] (Adeles → ℂ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let pairing (lam : Param) (b : FiniteAdelicGroupPoints F G) (a : InfiniteAdelicGroupPoints F G) :=
    complexParameterPairing F P lam (hK.height (pair F G a b))
  refine
    { toFun := fun lam g => groupDirectionalValue 𝓘∞ X (pairing lam (finite F G g)) (infinite F G g)
      map_add' := fun lam mu => ?_
      map_smul' := fun c lam => ?_ }
  · funext g
    have heq : pairing (lam + mu) (finite F G g) =
        pairing lam (finite F G g) + pairing mu (finite F G g) := by
      funext a
      simp [pairing, map_add]
    rw [heq, groupDirectionalValue_add _ _ (hH lam _) (hH mu _)]
    rfl
  · funext g
    have heq : pairing (c • lam) (finite F G g) = c • pairing lam (finite F G g) := by
      funext a
      simp [pairing, map_smul]
    rw [heq, groupDirectionalValue_const_smul _ _ _ (hH lam _)]
    rfl

private theorem parameterDirectionalSection_apply_add
    (hH : hK.HasSmoothHeightPairings hsmooth) (X : smoothModel F d) (φ : Adeles → ℂ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => φ (pair F G a b))) (lam : Param) (g : Adeles) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    hK.parameterDirectionalSection hsmooth lam X φ g =
      groupDirectionalValue 𝓘∞ X (fun a => φ (pair F G a (finite F G g))) (infinite F G g) +
        φ g * hK.heightPairingDirectional hsmooth hH X lam g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let f (a : InfiniteAdelicGroupPoints F G) := φ (pair F G a (finite F G g))
  let H (a : InfiniteAdelicGroupPoints F G) :=
    complexParameterPairing F P lam (hK.height (pair F G a (finite F G g)))
  let x := infinite F G g
  have hg : pair F G x (finite F G g) = g := pair_projections F G g
  change groupDirectionalValue 𝓘∞ X (fun a => f a * Complex.exp (H a)) x /
    hK.heightPower lam g = groupDirectionalValue 𝓘∞ X f x + φ g * groupDirectionalValue 𝓘∞ X H x
  rw [groupDirectionalValue_mul_cexp 𝓘∞ X (f := f) (h := H) (hφ _) (hH lam _) x]
  have hf : f x = φ g := congrArg φ hg
  have hpow : Complex.exp (H x) = hK.heightPower lam g :=
    congrArg (hK.heightPower lam) hg
  rw [hf, hpow, mul_div_cancel_right₀ _ (hK.heightPower_ne_zero lam g)]

/-- Transporting the derivative back through the twist gives an affine family.
Its constant term is the original invariant derivative at parameter zero. -/
theorem parameterDirectionalSection_eq_add
    (hH : hK.HasSmoothHeightPairings hsmooth) (X : smoothModel F d) (φ : Adeles → ℂ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => φ (pair F G a b))) (lam : Param) :
    hK.parameterDirectionalSection hsmooth lam X φ =
      hK.parameterDirectionalSection hsmooth 0 X φ + φ * hK.heightPairingDirectional hsmooth hH X lam := by
  funext g
  rw [Pi.add_apply, Pi.mul_apply, hK.parameterDirectionalSection_apply_add hsmooth hH X φ hφ lam g,
    hK.parameterDirectionalSection_apply_add hsmooth hH X φ hφ 0 g]
  simp

/-- In finite-dimensional linear parameter coordinates, invariant differentiation
of a constant section gives a finite holomorphic family of scalar sections. -/
theorem parameterDirectionalSection_mem_finiteHolomorphicSections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (e : E →ₗ[ℂ] Param) (hH : hK.HasSmoothHeightPairings hsmooth) (X : smoothModel F d)
    (φ : Adeles → ℂ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => φ (pair F G a b))) :
    (fun t => hK.parameterDirectionalSection hsmooth (e t) X φ) ∈
      finiteHolomorphicSections E (Adeles → ℂ) := by
  classical
  let D := (hK.heightPairingDirectional hsmooth hH X).comp e
  let basis := Module.finBasis ℂ E
  have hsum (t : E) : D t = ∑ j, basis.coord j t • D (basis j) := by
    have h := congrArg D (basis.sum_repr t)
    simpa only [map_sum, map_smul, Module.Basis.coord_apply] using h.symm
  have heq : (fun t => hK.parameterDirectionalSection hsmooth (e t) X φ) =
      (fun _ => hK.parameterDirectionalSection hsmooth 0 X φ) +
        (fun t => ∑ j, basis.coord j t • (φ * D (basis j))) := by
    funext t
    rw [hK.parameterDirectionalSection_eq_add hsmooth hH X φ hφ, Pi.add_apply]
    congr 1
    change φ * D t = _
    rw [hsum t, Finset.mul_sum]
    simp only [mul_smul_comm]
  rw [heq]
  exact (finiteHolomorphicSections E _).add_mem (FiniteHolomorphicSections.const_mem _)
    (FiniteHolomorphicSections.mem_iff.mpr
      ⟨_, fun j => basis.coord j, fun j => φ * D (basis j),
        fun j => (basis.coord j).toContinuousLinearMap.differentiable, fun _ => rfl⟩)

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
