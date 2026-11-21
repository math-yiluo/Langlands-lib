import Langlands.Global.AdelicEisensteinGrowthBound

/-! # Left translation of automorphic functions on actual adelic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.InfiniteAdelicGroupPoints
  Langlands.Global.RepresentationGrowth Langlands.GroupScheme Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

private theorem plotSmoothEnvelopingAction_leftTranslation
    (a : InfiniteAdelicGroupPoints F G)
    (D : AdelicEnvelopingAlgebra F G hsmooth) (f : InfinitePlotSmoothFunctions F G) :
    plotSmoothEnvelopingAction F G hsmooth hcalc D (plotSmoothLeftTranslation F G a f) =
      plotSmoothLeftTranslation F G a (plotSmoothEnvelopingAction F G hsmooth hcalc D f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  revert f
  obtain ⟨y, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) D
  change ∀ f, plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) (plotSmoothLeftTranslation F G a f) =
      plotSmoothLeftTranslation F G a (plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) f)
  induction y using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | «ι» X =>
    intro f
    change plotSmoothEnvelopingAction F G hsmooth hcalc (UniversalEnvelopingAlgebra.ι ℂ X)
        (plotSmoothLeftTranslation F G a f) =
      plotSmoothLeftTranslation F G a (plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ X) f)
    simp only [plotSmoothEnvelopingAction_generator]
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      simp only [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply, map_smul]
      exact congrArg (z • ·) (plotSmoothDifferential_leftTranslation F G hsmooth X a f)
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul y z hy hz =>
    intro f
    simp only [map_mul, Module.End.mul_apply, hy, hz]
  | add y z hy hz =>
    intro f
    simp only [map_add, LinearMap.add_apply, hy, hz]

omit [IsAffine G.X.left] in
private theorem HasModerateGrowthFunction.leftTranslate
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : HasModerateGrowthFunction F G rho φ) (a : AdelicGroupPoints F G) :
    HasModerateGrowthFunction F G rho (fun x => φ (a * x)) := by
  obtain ⟨r, hr, h⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height hφ
  obtain ⟨C, hC, hbound⟩ := h {1} isCompact_singleton
  have hbound' (x : AdelicGroupPoints F G) : ‖φ x‖ ≤ C * adelicHeightAtLeastOne rho x ^ r := by
    simpa only [mul_one] using hbound x 1 (Set.mem_singleton 1)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm (x : AdelicGroupPoints F G) : adelicMatrix F G rho x = 1 := by
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    let B := max 1 (AdelicMatrixHeight.height F 0 1)
    have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨C * B ^ r, mul_pos hC (Real.rpow_pos_of_pos hB _), 0, fun x => ?_⟩
    simpa only [Real.rpow_zero, mul_one, adelicHeightAtLeastOne, adelicHeight, hm, B] using hbound' (a * x)
  · let C₀ : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hC₀ : 0 < C₀ := pow_pos (Nat.cast_pos.mpr hN) _
    have hH (x : AdelicGroupPoints F G) : 0 < adelicHeight F G rho x :=
      zero_lt_one.trans_le (one_le_adelicHeight F G rho hN x)
    refine ⟨C * adelicHeight F G rho a ^ r * C₀ ^ r,
      mul_pos (mul_pos hC (Real.rpow_pos_of_pos (hH a) _)) (Real.rpow_pos_of_pos hC₀ _), r, fun x => ?_⟩
    calc
      ‖φ (a * x)‖ ≤ C * adelicHeight F G rho (a * x) ^ r := by
        simpa only [adelicHeightAtLeastOne_eq hN] using hbound' (a * x)
      _ ≤ C * (adelicHeight F G rho a * adelicHeight F G rho x) ^ r :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hH _).le (adelicHeight_mul_le F G rho hN a x) hr) hC.le
      _ = _ := by
        rw [Real.mul_rpow (hH a).le (hH x).le, adelicHeight_eq_scalar_mul_sourceNorm F G rho x]
        change C * (adelicHeight F G rho a ^ r * (C₀ * adelicSourceNorm F G rho x) ^ r) = _
        rw [Real.mul_rpow hC₀.le (adelicSourceNorm_pos F G rho hN x).le]
        ring

/-- An adelic left translation preserves automorphy with the corresponding
conjugate left invariance subgroup. -/
theorem IsAutomorphicFunctionOn.leftTranslate
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {Γ : Subgroup (AdelicGroupPoints F G)} {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ)
    (a : AdelicGroupPoints F G) :
    IsAutomorphicFunctionOn F G hsmooth hcalc (Γ.map (MulAut.conj a⁻¹).toMonoidHom) Kinf rho
      (fun x => φ (a * x)) := by
  let f : AdelicGroupPoints F G → ℂ := fun x => φ (a * x)
  obtain ⟨hInv, hSmooth, hKfinite, hCenter, hGrowth⟩ := hφ
  let aInf := infinite F G a
  let aFin := finite F G a
  let φslice (b : FiniteAdelicGroupPoints F G) : InfinitePlotSmoothFunctions F G :=
    ⟨functionInfiniteSlice F G φ (aFin * b), hSmooth.2.1 (aFin * b)⟩
  have hslice (b : FiniteAdelicGroupPoints F G) :
      functionInfiniteSlice F G f b = (plotSmoothLeftTranslation F G aInf (φslice b)).val := by
    funext x
    change φ (a * pair F G x b) = φ (pair F G (aInf * x) (aFin * b))
    conv_lhs => rw [← pair_projections F G a, pair_mul]
  refine ⟨?_, ?_, ?_, ?_, hGrowth.leftTranslate a⟩
  · rintro _ ⟨z, hz, rfl⟩ x
    change φ (a * ((a⁻¹ * z * a⁻¹⁻¹) * x)) = φ (a * x)
    rw [show a * ((a⁻¹ * z * a⁻¹⁻¹) * x) = z * (a * x) by group]
    exact hInv z hz (a * x)
  · obtain ⟨L, hL, hfix⟩ := hSmooth.2.2
    refine ⟨hSmooth.1.comp (continuous_const.mul continuous_id),
      fun b => (hslice b).symm ▸ (plotSmoothLeftTranslation F G aInf (φslice b)).2, L, hL, ?_⟩
    intro y hy x
    change φ (a * (x * ofFinite F G y)) = φ (a * x)
    exact (mul_assoc a x (ofFinite F G y)) ▸ hfix y hy (a * x)
  · let span (g : AdelicGroupPoints F G → ℂ) :=
      Submodule.span ℂ (Set.range fun k : Kinf =>
        fun x => g (x * ofInfinite F G k.val))
    let T : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
      { toFun := fun g x => g (a * x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let : FiniteDimensional ℂ (span φ) := hKfinite
    change FiniteDimensional ℂ (span f)
    apply Submodule.finiteDimensional_of_le (S₂ := (span φ).map T)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    funext x
    exact congrArg φ (mul_assoc a x (ofInfinite F G k.val))
  · obtain ⟨I, hI, hAnn⟩ := hCenter
    refine ⟨I, hI, fun z hz b hb => ?_⟩
    have heq : (⟨functionInfiniteSlice F G f b, hb⟩ : InfinitePlotSmoothFunctions F G) =
        plotSmoothLeftTranslation F G aInf (φslice b) := Subtype.ext (hslice b)
    rw [heq]
    have hzer : plotSmoothEnvelopingAction F G hsmooth hcalc z.val (φslice b) = 0 :=
      hAnn z hz (aFin * b) (hSmooth.2.1 (aFin * b))
    change plotSmoothEnvelopingAction F G hsmooth hcalc z.val
      (plotSmoothLeftTranslation F G aInf (φslice b)) = 0
    rw [plotSmoothEnvelopingAction_leftTranslation hcalc, hzer, map_zero]

/-- The fixed-compact automorphy predicate transports through adelic left
translation, including its center and growth requirements. -/
def AutomorphicLeftTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N d : ℕ) (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) (a : AdelicGroupPoints F G),
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ →
      IsAutomorphicFunctionOn F G hsmooth hcalc (Γ.map (MulAut.conj a⁻¹).toMonoidHom) Kinf rho
        (fun x => φ (a * x))

theorem automorphicLeftTranslation : AutomorphicLeftTranslationStatement.{u} := by
  intro F _ _ G _ N d rho hsmooth hcalc Γ Kinf φ a hφ
  exact IsAutomorphicFunctionOn.leftTranslate hcalc hφ a

end Langlands.Automorphic.GroupSchemeFunctions
