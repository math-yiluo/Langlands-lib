import Langlands.Automorphic.GroupSchemeParabolicTangentComparison
import Langlands.GroupScheme.Rational.ParabolicLieGrading
import Langlands.GroupScheme.Lie.ReductiveLieAlgebraCharZero
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.Algebra.LieCentralRadicalBaseChange
import Langlands.Algebra.BaseChangeEigenvectors
import Langlands.Algebra.LieEigenvectorTransport

/-! # The archimedean tangent grading of a rational parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
open Langlands.Algebra
open scoped Langlands.GroupScheme.Lie.FieldLie

section Rational

set_option backward.isDefEq.respectTransparency true

variable (F : Type u) [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- A rational vector lies in the image of the rational tangent map of a homomorphism exactly
when it lies in the image of the tangent map over `F`. -/
theorem mem_range_rationalTargetMap_iff (f : H ⟶ G) (x : RationalTangentLie F G) :
    x ∈ LinearMap.range (rationalTargetMap F f) ↔
      RestrictScalars.addEquiv ℚ F _ x ∈ LinearMap.range (Lie.targetMapLinear f F) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨RestrictScalars.addEquiv ℚ F _ y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨(RestrictScalars.addEquiv ℚ F _).symm y, (RestrictScalars.addEquiv ℚ F _).injective ?_⟩
    rw [rationalTargetMap_apply, AddEquiv.apply_symm_apply]
    exact hy

variable (G) in
/-- The eigenvectors of the rational inner derivation of `h`, for rational eigenvalues, are the
eigenvectors of the inner derivation of `h` over `F`. -/
theorem rationalAd_eigenSet (h : Additive (lieKernel G F)) {κ : Type*} (r : κ → ℚ) :
    {m : RationalTangentLie F G |
        ∃ i, LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm h) m =
          r i • m} =
      (RestrictScalars.addEquiv ℚ F _).symm '' {Y | ∃ i, ⁅h, Y⁆ = algebraMap ℚ F (r i) • Y} := by
  ext m
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨RestrictScalars.addEquiv ℚ F _ m, ⟨i, ?_⟩, AddEquiv.symm_apply_apply _ m⟩
    exact (congrArg (RestrictScalars.addEquiv ℚ F _) hi).trans
      (RestrictScalars.addEquiv_map_smul ℚ F _ (r i) m)
  · rintro ⟨Y, ⟨i, hi⟩, rfl⟩
    refine ⟨i, (RestrictScalars.addEquiv ℚ F _).injective ?_⟩
    have h2 : RestrictScalars.addEquiv ℚ F _ (r i • (RestrictScalars.addEquiv ℚ F _).symm Y) =
        algebraMap ℚ F (r i) • Y := by
      rw [RestrictScalars.addEquiv_map_smul, AddEquiv.apply_symm_apply]
    exact hi.trans h2.symm

omit [NumberField F] in
variable (G) in
/-- The eigenvectors of `ad h` for a family of eigenvalues form a set stable under scalars. -/
theorem smul_mem_eigenSet (h : Additive (lieKernel G F)) {κ : Type*} (r : κ → F) (c : F)
    (Y : Additive (lieKernel G F)) (hY : Y ∈ {Y | ∃ i, ⁅h, Y⁆ = r i • Y}) :
    c • Y ∈ {Y : Additive (lieKernel G F) | ∃ i, ⁅h, Y⁆ = r i • Y} := by
  obtain ⟨i, hi⟩ := hY
  exact ⟨i, by rw [lie_smul, hi, smul_comm]⟩

variable (G) in
/-- Integral eigenvectors spanning over `F` span over the rationals. -/
theorem rational_span_eigen_eq_top (h : Additive (lieKernel G F))
    (hspan : Submodule.span F {Y : Additive (lieKernel G F) | ∃ n : ℤ, ⁅h, Y⁆ = (n : F) • Y} = ⊤) :
    Submodule.span ℚ {m : RationalTangentLie F G | ∃ n : ℤ,
      LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm h) m =
        (n : ℚ) • m} = ⊤ := by
  have hset : {m : RationalTangentLie F G | ∃ n : ℤ,
      LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm h) m =
        (n : ℚ) • m} = (RestrictScalars.addEquiv ℚ F _).symm ''
          {Y : Additive (lieKernel G F) | ∃ n : ℤ, ⁅h, Y⁆ = (n : F) • Y} := by
    refine (rationalAd_eigenSet F G h (fun n : ℤ => (n : ℚ))).trans ?_
    congr 1
    ext Y
    simp only [Set.mem_ofPred_eq, map_intCast]
  rw [hset]
  exact LieEigenvectorTransport.span_restrictScalars_eq_top
    (smul_mem_eigenSet F G h (fun n : ℤ => (n : F))) hspan

variable (G) in
/-- The span of the eigenvectors with positive integral eigenvalues, over the rationals. -/
theorem mem_rational_span_positive_eigen_iff (h : Additive (lieKernel G F))
    (x : RationalTangentLie F G) :
    x ∈ Submodule.span ℚ {m : RationalTangentLie F G | ∃ n : ℕ,
      LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm h) m =
        ((n + 1 : ℕ) : ℚ) • m} ↔
      RestrictScalars.addEquiv ℚ F _ x ∈ Submodule.span F
        {Y : Additive (lieKernel G F) | ∃ n : ℕ, ⁅h, Y⁆ = ((n + 1 : ℕ) : F) • Y} := by
  have hset : {m : RationalTangentLie F G | ∃ n : ℕ,
      LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm h) m =
        ((n + 1 : ℕ) : ℚ) • m} = (RestrictScalars.addEquiv ℚ F _).symm ''
          {Y : Additive (lieKernel G F) | ∃ n : ℕ, ⁅h, Y⁆ = ((n + 1 : ℕ) : F) • Y} := by
    refine (rationalAd_eigenSet F G h (fun n : ℕ => ((n + 1 : ℕ) : ℚ))).trans ?_
    congr 1
    ext Y
    simp only [Set.mem_ofPred_eq, map_natCast]
  rw [hset]
  exact LieEigenvectorTransport.mem_span_restrictScalars_iff
    (smul_mem_eigenSet F G h (fun n : ℕ => ((n + 1 : ℕ) : F))) x

end Rational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **The archimedean tangent grading of a rational parabolic.** -/
theorem parabolicLeviTangentGrading : ParabolicLeviTangentGradingStatement.{u} := by
  intro F _ _ G Q M V _ _ _ q iV l hG hq hV hl _ d e c hGs hMs hVs
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := @SmoothOfRelativeDimension.smooth d _ _ G.X.hom hGs
  have : Smooth M.X.hom := @SmoothOfRelativeDimension.smooth e _ _ M.X.hom hMs
  have : Smooth V.X.hom := @SmoothOfRelativeDimension.smooth c _ _ V.X.hom hVs
  obtain ⟨H₀, hspan, hinj, hlevi, hrad⟩ := Lie.exists_parabolicLieGrading q iV l hG hq hV hl
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hGs
  let := smoothLieGroup F G hGs
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  -- the rational data
  have hT := rational_span_eigen_eq_top F G H₀ hspan
  -- reductivity
  have hredF : LieAlgebra.HasCentralRadical F (Additive (lieKernel G F)) :=
    Lie.hasCentralRadical_of_isConnectedReductive G hG
  have hredQ : LieAlgebra.HasCentralRadical ℂ (ℂ ⊗[ℚ] RationalTangentLie F G) :=
    LieCentralRadical.hasCentralRadical_baseChange_restrictScalars
  have := finite_rationalTangentLie F G
  have : FiniteDimensional ℂ (AdelicComplexLieAlgebra F G hGs) :=
    (complexTangentEquiv F G hGs).toLinearEquiv.finiteDimensional
  have hred : LieAlgebra.HasCentralRadical ℂ (AdelicComplexLieAlgebra F G hGs) :=
    LieCentralRadical.hasCentralRadical_of_lieEquiv (complexTangentEquiv F G hGs)
  refine ⟨hred.radical_eq_center,
    complexTangentEquiv F G hGs ((1 : ℂ) ⊗ₜ (RestrictScalars.addEquiv ℚ F _).symm H₀),
    ?_, ?_, ?_, ?_⟩
  · -- integral eigenvectors span
    have h1 : Submodule.span ℂ {X : ℂ ⊗[ℚ] RationalTangentLie F G | ∃ i : ℤ,
        ⁅(1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀, X⁆ = (i : ℂ) • X} = ⊤ := by
      have hset : {X : ℂ ⊗[ℚ] RationalTangentLie F G | ∃ i : ℤ,
          ⁅(1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀, X⁆ = (i : ℂ) • X} =
          {X | ∃ n : ℤ, (LieAlgebra.ad ℚ (RationalTangentLie F G)
            ((RestrictScalars.addEquiv ℚ F _).symm H₀)).baseChange ℂ X = (n : ℂ) • X} := by
        ext X
        simp only [Set.mem_ofPred_eq, LieEigenvectorTransport.one_tmul_lie]
      rw [hset]
      exact BaseChangeEigenvectors.span_baseChange_eigen_eq_top _ hT
    refine (@LieEigenvectorTransport.span_eigenSet_eq_map ℂ _ _ _ _ _ _ _
      (complexTangentEquiv F G hGs)
      ((1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀) _ (fun k : ℤ => (k : ℂ))).trans ?_
    show Submodule.map _ (Submodule.span ℂ {X : ℂ ⊗[ℚ] RationalTangentLie F G | ∃ i : ℤ,
        ⁅(1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀, X⁆ = (i : ℂ) • X}) = ⊤
    rw [h1, Submodule.map_top, LinearEquiv.range]
  · -- the Levi differential is injective
    intro Y₁ Y₂ hY
    obtain ⟨t₁, rfl⟩ := complexTangentMap_surjective F M hMs Y₁
    obtain ⟨t₂, rfl⟩ := complexTangentMap_surjective F M hMs Y₂
    rw [complexPointDifferential_complexTangentMap, complexPointDifferential_complexTangentMap] at hY
    have hinjQ : Function.Injective (rationalTargetMap F (l ≫ q)) := by
      intro x y hxy
      apply (RestrictScalars.addEquiv ℚ F _).injective
      apply hinj
      exact congrArg (RestrictScalars.addEquiv ℚ F _) hxy
    have hbc : Function.Injective ((rationalTargetMap F (l ≫ q)).baseChange ℂ) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ hinjQ
    rw [hbc (complexTangentMap_injective F G hGs hY)]
  · -- the image of the Levi differential is the centralizer
    intro Y
    obtain ⟨X, rfl⟩ := complexTangentMap_surjective F G hGs Y
    have hr : complexTangentMap F G hGs X ∈
        LinearMap.range (complexPointDifferential F hMs hGs (l ≫ q)) ↔
          X ∈ LinearMap.range ((rationalTargetMap F (l ≫ q)).baseChange ℂ) := by
      constructor
      · rintro ⟨Z, hZ⟩
        obtain ⟨t, rfl⟩ := complexTangentMap_surjective F M hMs Z
        rw [complexPointDifferential_complexTangentMap] at hZ
        exact ⟨t, complexTangentMap_injective F G hGs hZ⟩
      · rintro ⟨t, rfl⟩
        exact ⟨complexTangentMap F M hMs t,
          complexPointDifferential_complexTangentMap F hMs hGs (l ≫ q) t⟩
    have hb : LinearMap.range (rationalTargetMap F (l ≫ q)) = LinearMap.ker
        (LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm H₀)) := by
      ext x
      rw [mem_range_rationalTargetMap_iff, hlevi, LinearMap.mem_ker]
      constructor
      · intro h
        apply (RestrictScalars.addEquiv ℚ F _).injective
        exact h.trans (map_zero _).symm
      · intro h
        exact (congrArg (RestrictScalars.addEquiv ℚ F _) h).trans (map_zero _)
    have hl0 := @LieEigenvectorTransport.lie_eq_smul_iff ℂ _ _ _ _ _ _ _
      (complexTangentEquiv F G hGs) ((1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀) X 0
    rw [zero_smul, zero_smul] at hl0
    rw [hr]
    refine Iff.trans ?_ hl0.symm
    rw [LieEigenvectorTransport.one_tmul_lie, BaseChangeEigenvectors.range_baseChange_eq hb,
      ← BaseChangeEigenvectors.ker_baseChange, LinearMap.mem_ker]
  · -- the image of the radical differential is the positive part
    have hc : LinearMap.range (rationalTargetMap F (iV ≫ q)) =
        Submodule.span ℚ {m : RationalTangentLie F G | ∃ n : ℕ,
          LieAlgebra.ad ℚ (RationalTangentLie F G) ((RestrictScalars.addEquiv ℚ F _).symm H₀) m =
            ((n + 1 : ℕ) : ℚ) • m} := by
      ext x
      rw [mem_range_rationalTargetMap_iff, hrad, mem_rational_span_positive_eigen_iff]
    have h1 : LinearMap.range (complexPointDifferential F hVs hGs (iV ≫ q)) =
        (LinearMap.range ((rationalTargetMap F (iV ≫ q)).baseChange ℂ)).map
          (complexTangentMap F G hGs) := by
      ext Y
      constructor
      · rintro ⟨Z, rfl⟩
        obtain ⟨t, rfl⟩ := complexTangentMap_surjective F V hVs Z
        exact ⟨_, ⟨t, rfl⟩, (complexPointDifferential_complexTangentMap F hVs hGs (iV ≫ q) t).symm⟩
      · rintro ⟨X, ⟨t, rfl⟩, rfl⟩
        exact ⟨complexTangentMap F V hVs t,
          complexPointDifferential_complexTangentMap F hVs hGs (iV ≫ q) t⟩
    have h2 : Submodule.span ℂ {X : ℂ ⊗[ℚ] RationalTangentLie F G | ∃ k : ℕ,
        ⁅(1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀, X⁆ = ((k + 1 : ℕ) : ℂ) • X} =
          LinearMap.range ((rationalTargetMap F (iV ≫ q)).baseChange ℂ) := by
      rw [BaseChangeEigenvectors.range_baseChange_eq hc,
        ← BaseChangeEigenvectors.span_baseChange_positive_eigen]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq, LieEigenvectorTransport.one_tmul_lie]
    rw [h1, ← h2]
    exact (@LieEigenvectorTransport.span_eigenSet_eq_map ℂ _ _ _ _ _ _ _
      (complexTangentEquiv F G hGs)
      ((1 : ℂ) ⊗ₜ[ℚ] (RestrictScalars.addEquiv ℚ F _).symm H₀) _
      (fun k : ℕ => ((k + 1 : ℕ) : ℂ))).symm

end Langlands.Automorphic.GroupSchemeFunctions
