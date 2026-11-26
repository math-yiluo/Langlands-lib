import Langlands.Geometry.Manifold.SmoothGroupLieDifferential
import Langlands.Geometry.Manifold.VectorFieldCommutator
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Mathlib.Geometry.Manifold.BumpFunction

/-! # Tangent maps of smooth group homomorphisms and smooth characters -/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

section Hom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

/-- The derivative at the identity of a group homomorphism, as a map of identity tangent
spaces. -/
def groupHomTangent (φ : G →* G') : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G' :=
  mfderiv I I' φ 1

omit [LieGroup I ∞ G] in
/-- Chain rule for the positive right-orbit derivative along a smooth homomorphism. -/
theorem groupDirectionalValue_comp_hom (φ : G →* G') (hφ : ContMDiff I I' ∞ φ)
    (X : GroupLieAlgebra I G) {f : G' → ℂ} (hf : ContMDiff I' 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    groupDirectionalValue I X (fun x => f (φ x)) g =
      groupDirectionalValue I' (groupHomTangent I I' φ X) f (φ g) := by
  have horbit : ContMDiff I' 𝓘(ℝ, ℂ) ∞ (fun k : G' => f (φ g * k)) :=
    hf.comp (contMDiff_const.mul contMDiff_id)
  have heq : (fun h : G => f (φ (g * h))) = (fun k : G' => f (φ g * k)) ∘ φ := by
    funext h
    simp only [Function.comp_apply, map_mul]
  change mvfderiv I (fun h => f (φ (g * h))) 1 X =
    mvfderiv I' (fun k => f (φ g * k)) 1 (mfderiv I I' φ 1 X)
  rw [heq, mvfderiv_comp_apply_of_eq (1 : G) (horbit.mdifferentiableAt (by simp))
    (hφ.mdifferentiableAt (by simp)) (map_one φ)]

omit [LieGroup I ∞ G] in
/-- The orbit derivative at the identity is the manifold derivative. -/
theorem groupDirectionalValue_one (X : GroupLieAlgebra I G) (f : G → ℂ) :
    groupDirectionalValue I X f 1 = mvfderiv I f 1 X := by
  simp only [groupDirectionalValue, one_mul]

variable [CompleteSpace E] [I.Boundaryless] [CompleteSpace E'] [I'.Boundaryless]

/-- If smooth functions separate the identity tangent vectors of the target, the tangent map
of a smooth homomorphism preserves the Lie bracket of left-invariant vector fields. -/
theorem groupHomTangent_lie_of_separating (φ : G →* G') (hφ : ContMDiff I I' ∞ φ)
    (hsep : ∀ W : GroupLieAlgebra I' G',
      (∀ f : G' → ℂ, ContMDiff I' 𝓘(ℝ, ℂ) ∞ f → mvfderiv I' f 1 W = 0) → W = 0)
    (X Y : GroupLieAlgebra I G) :
    groupHomTangent I I' φ ⁅X, Y⁆ =
      ⁅groupHomTangent I I' φ X, groupHomTangent I I' φ Y⁆ := by
  rw [← sub_eq_zero]
  apply hsep
  intro f hf
  have hcalc := smoothVectorFieldCommutator_proof (I := I) (M := G)
  have hcalc' := smoothVectorFieldCommutator_proof (I := I') (M := G')
  have hfφ : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => f (φ x)) := hf.comp hφ
  have hcomp (Z : GroupLieAlgebra I G) :
      groupDirectionalValue I Z (fun x => f (φ x)) =
        fun x => groupDirectionalValue I' (groupHomTangent I I' φ Z) f (φ x) :=
    funext (groupDirectionalValue_comp_hom I I' φ hφ Z hf)
  have hcomp₂ (Z W : GroupLieAlgebra I G) :
      groupDirectionalValue I Z (groupDirectionalValue I W (fun x => f (φ x))) 1 =
        groupDirectionalValue I' (groupHomTangent I I' φ Z)
          (groupDirectionalValue I' (groupHomTangent I I' φ W) f) 1 := by
    rw [hcomp W, groupDirectionalValue_comp_hom I I' φ hφ Z
      (contMDiff_groupDirectionalValue I' _ hf), map_one]
  have h₁ := groupDirectionalValue_commutator_of_vectorFieldCommutator I hcalc X Y hfφ 1
  have h₂ := groupDirectionalValue_commutator_of_vectorFieldCommutator I' hcalc'
    (groupHomTangent I I' φ X) (groupHomTangent I I' φ Y) hf 1
  rw [groupDirectionalValue_comp_hom I I' φ hφ _ hf, map_one, hcomp₂, hcomp₂, ← h₂] at h₁
  rw [map_sub, ← groupDirectionalValue_one, ← groupDirectionalValue_one, h₁, sub_self]

end Hom

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Smooth complex functions separate the tangent vectors at every point of a
finite-dimensional Hausdorff manifold. -/
theorem eq_zero_of_forall_mvfderiv_eq_zero (x : M) (W : TangentSpace I x)
    (hW : ∀ f : M → ℂ, ContMDiff I 𝓘(ℝ, ℂ) ∞ f → mvfderiv I f x W = 0) : W = 0 := by
  let b : SmoothBumpFunction I x := Classical.arbitrary _
  let φ := extChartAt I x
  have hφ : MDifferentiableAt I 𝓘(ℝ, E) φ x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have hD : mfderiv I 𝓘(ℝ, E) φ x W = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff ℝ _).mp
    intro ℓ
    let L : E →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ℓ)
    let g : M → ℂ := fun y => L (φ y)
    have hg : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ g (chartAt H x).source :=
      (L.contDiff (n := ∞)).contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
    have hf := b.contMDiff_smul hg
    have heq : (fun y => b y • g y) =ᶠ[𝓝 x] g := by
      filter_upwards [b.eventuallyEq_one] with y hy
      rw [hy, Pi.one_apply, one_smul]
    have hgd : HasMFDerivAt I 𝓘(ℝ, ℂ) g x (L.comp (mfderiv I 𝓘(ℝ, E) φ x)) :=
      L.hasMFDerivAt.comp x hφ.hasMFDerivAt
    have hbd : HasMFDerivAt I 𝓘(ℝ, ℂ) (fun y => b y • g y) x
        (L.comp (mfderiv I 𝓘(ℝ, E) φ x)) :=
      hgd.congr_of_eventuallyEq heq
    have hval : mvfderiv I (fun y => b y • g y) x W = L (mfderiv I 𝓘(ℝ, E) φ x W) := by
      simp only [mvfderiv]
      rw [hbd.mfderiv]
      rfl
    have h := hW _ hf
    rw [hval] at h
    have h' : ((ℓ (mfderiv I 𝓘(ℝ, E) φ x W) : ℝ) : ℂ) = 0 := h
    exact_mod_cast h'
  have hinv := isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source (I := I) x)
  obtain ⟨e, he⟩ := hinv
  have h1 : (e : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, E) (extChartAt I x x)) W = 0 := by
    rw [he]
    exact hD
  have h2 : e W = 0 := h1
  exact e.map_eq_zero_iff.mp h2

end Separation

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The orbit derivative of a smooth multiplicative function is its derivative at the
identity times its value. -/
theorem groupDirectionalValue_character {χ : G → ℂ} (hχ : ∀ x y, χ (x * y) = χ x * χ y)
    (hχs : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ) (X : GroupLieAlgebra I G) (g : G) :
    groupDirectionalValue I X χ g = χ g * mvfderiv I χ 1 X := by
  have h := groupDirectionalValue_const_smul I X (χ g) hχs 1
  have he : (χ g • χ) = fun y => χ (g * y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, hχ]
  rw [he, groupDirectionalValue_one, groupDirectionalValue_one] at h
  rw [groupDirectionalValue, h, smul_eq_mul]

variable [CompleteSpace E] [I.Boundaryless]

/-- The derivative at the identity of a smooth multiplicative function vanishes on brackets. -/
theorem mvfderiv_character_lie {χ : G → ℂ} (hχ : ∀ x y, χ (x * y) = χ x * χ y)
    (hχs : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ) (X Y : GroupLieAlgebra I G) :
    mvfderiv I χ 1 ⁅X, Y⁆ = 0 := by
  have hcalc := smoothVectorFieldCommutator_proof (I := I) (M := G)
  have h := groupDirectionalValue_commutator_of_vectorFieldCommutator I hcalc X Y hχs 1
  have hD (Z : GroupLieAlgebra I G) :
      groupDirectionalValue I Z χ = mvfderiv I χ 1 Z • χ := by
    funext g
    rw [groupDirectionalValue_character I hχ hχs, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [← groupDirectionalValue_one, h, hD Y, hD X,
    groupDirectionalValue_const_smul I X _ hχs, groupDirectionalValue_const_smul I Y _ hχs,
    smul_eq_mul, smul_eq_mul, groupDirectionalValue_one, groupDirectionalValue_one, mul_comm,
    sub_self]

end Character

end Langlands.Geometry.Manifold
