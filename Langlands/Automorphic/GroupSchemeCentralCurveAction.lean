import Langlands.Automorphic.GroupSchemeForms
import Langlands.Global.InfiniteAdelicChartFormula
import Langlands.Global.InfinitePlaceMatrixRealization
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Langlands.Algebra.SignedCartanCasimir
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof

/-! # Central curves and their actual archimedean differential action -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

section CurveDerivative

variable {W M : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Group M] [TopologicalSpace M] [ChartedSpace W M] [LieGroup 𝓘(ℝ, W) ∞ M]

local notation "I" => 𝓘(ℝ, W)
local notation "IR" => 𝓘(ℝ, ℝ)
local notation "IC" => 𝓘(ℝ, ℂ)

omit [Group M] [LieGroup I ∞ M] in
private theorem deriv_comp_curve_zero (c : ℝ → M) (hc : ContMDiff IR I ∞ c)
    (f : M → ℂ) (hf : ContMDiff I IC ∞ f) :
    deriv (f ∘ c) 0 = mvfderiv I f (c 0) (mfderiv IR I c 0 (1 : ℝ)) := by
  rw [← fderiv_apply_one_eq_deriv,
    show fderiv ℝ (f ∘ c) 0 1 = mvfderiv IR (f ∘ c) 0 1 from
      (DFunLike.congr_fun (mvfderiv_eq_fderiv (f := f ∘ c) (x := 0)) 1).symm]
  exact mvfderiv_comp_apply 0 (hf.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp)) 1

/-- The derivative along a smooth one-parameter subgroup is the right-orbit derivative
in its actual tangent direction. -/
theorem hasDerivAt_mul_smoothOneParameter (c : ℝ → M) (hc : ContMDiff IR I ∞ c)
    (h0 : c 0 = 1) (ha : ∀ s t, c (s + t) = c s * c t)
    (f : M → ℂ) (hf : ContMDiff I IC ∞ f) (g : M) (t : ℝ) :
    HasDerivAt (fun s => f (g * c s))
      (groupDirectionalValue I (mfderiv IR I c 0 (1 : ℝ)) f (g * c t)) t := by
  let b (y : M) := f ((g * c t) * y)
  have hb : ContMDiff I IC ∞ b := hf.comp (contMDiff_const.mul contMDiff_id)
  have hb' : HasDerivAt (b ∘ c)
      (groupDirectionalValue I (mfderiv IR I c 0 (1 : ℝ)) f (g * c t)) 0 := by
    have hderiv := (hb.comp hc).contDiff.differentiable (by simp) (0 : ℝ)
    convert hderiv.hasDerivAt using 1
    rw [deriv_comp_curve_zero c hc b hb]
    change mvfderiv I b 1 _ = mvfderiv I b (c 0) _
    rw [h0]
  have ht : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h := hb'.scomp_of_eq t ht (sub_self t).symm
  rw [one_smul] at h
  convert h using 1
  funext s
  have hs : t + (s - t) = s := by ring
  simp only [Function.comp_apply, b, mul_assoc, ← ha, hs]

end CurveDerivative

section MatrixCurve

open MatrixCoefficientLie

variable {W M K n : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Group M] [TopologicalSpace M] [ChartedSpace W M]
  [NormedRing K] [NormedAlgebra ℝ K] [Fintype n] [DecidableEq n]

local notation "I" => 𝓘(ℝ, W)

/-- The matrix differential of a central smooth curve through the identity commutes
with the matrix differentials of all tangent directions. -/
theorem matrixDifferential_commute_of_centralCurve (φ : M →* Matrix n n K)
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, K) ∞ (fun g => φ g a b))
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (h0 : c 0 = 1)
    (hcent : ∀ t g, Commute (c t) g) (Y : GroupLieAlgebra I M) :
    Commute (matrixDifferential I φ (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ)))
      (matrixDifferential I φ Y) := by
  let X : GroupLieAlgebra I M := mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ)
  let A := matrixDifferential I φ X
  have hA (g : M) : A * φ g = φ g * A := by
    ext i j
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    let f (P Q : Matrix n n K) (y : M) := (ℓ ((P * φ y * Q) i j) : ℂ)
    have htest (P Q : Matrix n n K) : deriv (f P Q ∘ c) 0 = (ℓ ((P * A * Q) i j) : ℂ) := by
      rw [deriv_comp_curve_zero c hc _ (contMDiff_test hφ P Q ℓ i j), h0]
      exact mvfderiv_test hφ P Q ℓ i j 1 X
    have he : f 1 (φ g) ∘ c = f (φ g) 1 ∘ c := by
      funext t
      simp only [Function.comp_apply, f, one_mul, mul_one]
      rw [((hcent t g).map φ).eq]
    have h := (htest 1 (φ g)).symm.trans ((congrArg (fun s => deriv s 0) he).trans (htest (φ g) 1))
    simp only [one_mul, mul_one] at h
    exact Complex.ofReal_injective h
  change A * matrixDifferential I φ Y = matrixDifferential I φ Y * A
  ext i j
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  let f (P Q : Matrix n n K) (y : M) := (ℓ ((P * φ y * Q) i j) : ℂ)
  have he : f A 1 = f 1 A := by
    funext y
    simp only [f, mul_one, one_mul, hA y]
  have h := congrArg (fun s : M → ℂ => mvfderiv I s 1 Y) he
  change mvfderiv I (f A 1) 1 Y = mvfderiv I (f 1 A) 1 Y at h
  have hl : mvfderiv I (f A 1) 1 Y =
      (ℓ ((A * matrixDifferential I φ Y * 1 : Matrix n n K) i j) : ℂ) := mvfderiv_test hφ A 1 ℓ i j 1 Y
  have hr : mvfderiv I (f 1 A) 1 Y =
      (ℓ ((1 * matrixDifferential I φ Y * A : Matrix n n K) i j) : ℂ) := mvfderiv_test hφ 1 A ℓ i j 1 Y
  rw [hl, hr, mul_one, one_mul] at h
  exact Complex.ofReal_injective h

end MatrixCurve

end Langlands.Geometry.Manifold

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold Langlands.Geometry.Manifold.MatrixCoefficientLie
  Langlands.Geometry.Manifold.ZeroDirectionalDerivative

/-- A smooth central curve through identity differentiates to a central generator in the
actual complex enveloping algebra. -/
def CentralCurveEnvelopingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsConnectedReductive G →
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
      LieGroup.of_le (n := ∞) (by simp)
    ∀ c : ℝ → InfiniteAdelicGroupPoints F G,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c → c 0 = 1 → (∀ t g, Commute (c t) g) →
      UniversalEnvelopingAlgebra.ι ℂ
        (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
        ((1 : ℂ) ⊗ₜ[ℝ]
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ))) ∈
        Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 600000 in
/-- Differentiate centrality in each closed local realization, then use injectivity of
the realization differentials and the real-generator criterion for the center. -/
theorem centralCurveEnveloping : CentralCurveEnvelopingStatement.{u} := by
  classical
  intro F _ _ G _ d hsmooth hG
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  intro c hc h0 hcent
  let X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ)
  change Langlands.Algebra.SignedCartanCasimir.realGenerator X ∈
    Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)
  apply Langlands.Algebra.SignedCartanCasimir.mem_center_of_commute_real
  intro Y
  obtain ⟨N, ρ₀, hρ₀, _⟩ := InfinitePlaceGroupPoints.exists_closedMatrixRealization G hG
  let ρ (v : NumberField.InfinitePlace F) :
      MatrixRepresentation (InfinitePlaceGroupPoints.completionBaseChange F G v) (Fin N) :=
    ρ₀.baseChange (Spec.algebraMap F v.Completion)
  have hρ (v : NumberField.InfinitePlace F) : IsClosedSubgroup (ρ v) :=
    ρ₀.isClosedSubgroup_baseChange _ hρ₀
  have hXY : ⁅Y, X⁆ = 0 := by
    apply eq_zero_of_zeroDeriv_realization F G hsmooth ρ hρ ⁅Y, X⁆
    intro v a b
    let R := InfinitePlaceGroupPoints.realizationMatrix F G v (ρ v)
    let φ := (Units.coeHom _).comp (R.comp (atPlace F G v).toMonoidHom)
    have hp : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, Fin d → v.Completion) ∞ (atPlace F G v) :=
      (contMDiff_iff_places F G 𝓘(ℝ, smoothModel F d) hsmooth id).mp contMDiff_id v
    have he : ∀ a b, ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
        (fun g => φ g a b) :=
      (InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix F G v 𝓘(ℝ, smoothModel F d)
        hsmooth (ρ v) (hρ v) (atPlace F G v)).mp hp
    have h := matrixDifferential_lie φ he Y X
    have hcomm := matrixDifferential_commute_of_centralCurve φ he c hc h0 hcent Y
    change Commute (matrixDifferential 𝓘(ℝ, smoothModel F d) φ X)
      (matrixDifferential 𝓘(ℝ, smoothModel F d) φ Y) at hcomm
    rw [hcomm.symm.eq, sub_self] at h
    refine ⟨mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (fun g => φ g a b) 1,
      ((he a b).mdifferentiableAt (by simp)).hasMFDerivAt, ?_⟩
    exact congrArg (fun m => m a b) h
  have h := (Langlands.Algebra.SignedCartanCasimir.realGenerator.map_lie Y X).symm
  rw [hXY, map_zero] at h
  exact sub_eq_zero.mp h

end Langlands.Automorphic.GroupSchemeFunctions
