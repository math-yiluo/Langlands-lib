import Langlands.Global.AdelicRightConvolutionDifferentiation

/-! # Transport of actual adelic enveloping derivatives to a test kernel -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj ContDiff Manifold Pointwise TensorProduct

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

private theorem complexEnveloping_induction {L : Type u} [LieRing L] [LieAlgebra ℝ L]
    {P : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) → Prop}
    (h1 : P 1) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x))
    (hgen : ∀ (X : L) x, P x → P (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * x))
    (a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) : P a := by
  have hcomplex (Z : ℂ ⊗[ℝ] L) : ∀ b, P b → P (UniversalEnvelopingAlgebra.ι ℂ Z * b) := by
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      intro b hb
      have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, smul_mul_assoc]
      exact hsmul _ _ (hgen X b hb)
    | add Z W hZ hW =>
      intro b hb
      rw [map_add, add_mul]
      exact hadd _ _ (hZ b hb) (hW b hb)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] L)) a
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)
  have hq (t : TensorAlgebra ℂ (ℂ ⊗[ℝ] L)) : ∀ b, P b → P (q t * b) := by
    induction t using TensorAlgebra.induction with
    | algebraMap c =>
      intro b hb
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact hsmul _ _ hb
    | «ι» Z => exact hcomplex Z
    | mul t s ht hs =>
      intro b hb
      rw [map_mul, mul_assoc]
      exact ht _ (hs b hb)
    | add t s ht hs =>
      intro b hb
      rw [map_add, add_mul]
      exact hadd _ _ (ht b hb) (hs b hb)
  change P (q t)
  simpa only [mul_one] using hq t 1 h1

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

private theorem testFunction_add {h k : AdelicGroupPoints F G → ℂ}
    (hh : IsAdelicTestFunction F G h) (hk : IsAdelicTestFunction F G k) :
    IsAdelicTestFunction F G (h + k) := by
  obtain ⟨Lu, hLuo, hLu⟩ := hh.1.2.2
  obtain ⟨Lv, hLvo, hLv⟩ := hk.1.2.2
  obtain ⟨U, hUo, hU⟩ := hh.2.2
  obtain ⟨V, hVo, hV⟩ := hk.2.2
  refine ⟨⟨hh.1.1.add hk.1.1, ?_, Lu ⊓ Lv, hLuo.inter hLvo, ?_⟩,
    hh.2.1.add hk.2.1, U ⊓ V, hUo.inter hVo, ?_⟩
  · exact fun b => (InfinitePlotSmoothFunctions F G).add_mem (hh.1.2.1 b) (hk.1.2.1 b)
  · intro l hl x
    exact congrArg₂ (· + ·) (hLu l hl.1 x) (hLv l hl.2 x)
  · intro l hl x
    exact congrArg₂ (· + ·) (hU l hl.1 x) (hV l hl.2 x)

private theorem testFunction_smul {h : AdelicGroupPoints F G → ℂ}
    (hh : IsAdelicTestFunction F G h) (c : ℂ) : IsAdelicTestFunction F G (c • h) := by
  obtain ⟨L, hLo, hL⟩ := hh.1.2.2
  obtain ⟨U, hUo, hU⟩ := hh.2.2
  refine ⟨⟨hh.1.1.const_smul c, ?_, L, hLo, ?_⟩, hh.2.1.smul_left, U, hUo, ?_⟩
  · exact fun b => (InfinitePlotSmoothFunctions F G).smul_mem c (hh.1.2.1 b)
  · exact fun l hl x => congrArg (c • ·) (hL l hl x)
  · exact fun l hl x => congrArg (c • ·) (hU l hl x)

variable [LocallyOfFiniteType G.X.hom] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "μG" => (Measure.haar : Measure (AdelicGroupPoints F G))
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth

/-- The actual right convolution restricted to a fixed finite coordinate, as a smooth slice. -/
def rightConvolutionSmoothSlice (h f : AdelicGroupPoints F G → ℂ)
    (hh : IsAdelicTestFunction F G h) (hf : Measurable f) (hfi : LocallyIntegrable f μG)
    (b : FiniteAdelicGroupPoints F G) : InfinitePlotSmoothFunctions F G :=
  ⟨fun a => rightConvolution F G h f (pair F G a b),
    (adelicRightConvolutionDifferentiation F G d hsmooth h f hh hf hfi).2.1.2.1 b⟩

variable (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Each enveloping derivative of right convolution is represented by one test kernel
with the same support bound, chosen independently of the locally integrable input. -/
def AdelicRightConvolutionEnvelopingStatement : Prop :=
  ∀ (a : UEA) (h : AdelicGroupPoints F G → ℂ) (hh : IsAdelicTestFunction F G h),
    ∃ k : AdelicGroupPoints F G → ℂ, ∃ hk : IsAdelicTestFunction F G k,
      tsupport k ⊆ tsupport h ∧
      ∀ (f : AdelicGroupPoints F G → ℂ) (hf : Measurable f) (hfi : LocallyIntegrable f μG)
        (b : FiniteAdelicGroupPoints F G),
        plotSmoothEnvelopingAction F G hsmooth hcalc a
            (rightConvolutionSmoothSlice hsmooth h f hh hf hfi b) =
          rightConvolutionSmoothSlice hsmooth k f hk hf hfi b

theorem adelicRightConvolutionEnveloping : AdelicRightConvolutionEnvelopingStatement hsmooth hcalc := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup I∞ (minSmoothness ℝ 3) A∞ := LieGroup.of_le (n := ∞) (by simp)
  intro a h hh
  let S (k f : AdelicGroupPoints F G → ℂ) (hk : IsAdelicTestFunction F G k)
      (hf : Measurable f) (hfi : LocallyIntegrable f μG) (b : FiniteAdelicGroupPoints F G) :=
    rightConvolutionSmoothSlice hsmooth k f hk hf hfi b
  let D := plotSmoothEnvelopingAction F G hsmooth hcalc
  let P (a : UEA) : Prop := ∃ k : AdelicGroupPoints F G → ℂ, ∃ hk : IsAdelicTestFunction F G k,
    tsupport k ⊆ tsupport h ∧ ∀ f hf hfi b, D a (S h f hh hf hfi b) = S k f hk hf hfi b
  change P a
  induction a using complexEnveloping_induction with
  | h1 =>
    exact ⟨h, hh, Subset.rfl, fun f hf hfi b => by simp only [map_one, Module.End.one_apply]⟩
  | hadd a c ha hc =>
    obtain ⟨k, hk, hks, heq⟩ := ha
    obtain ⟨l, hl, hls, heq'⟩ := hc
    refine ⟨k + l, testFunction_add hk hl, (tsupport_add _ _).trans (union_subset hks hls), ?_⟩
    intro f hf hfi b
    rw [map_add, LinearMap.add_apply, heq, heq']
    apply Subtype.ext
    funext x
    change rightConvolution F G k f (pair F G x b) + rightConvolution F G l f (pair F G x b) =
      rightConvolution F G (k + l) f (pair F G x b)
    rw [rightConvolution, rightConvolution, rightConvolution]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add
      ((adelicRightConvolutionDifferentiation F G d hsmooth k f hk hf hfi).1 _)
      ((adelicRightConvolutionDifferentiation F G d hsmooth l f hl hf hfi).1 _)).symm
  | hsmul c a ha =>
    obtain ⟨k, hk, hks, heq⟩ := ha
    have hs : tsupport (c • k) ⊆ tsupport k :=
      tsupport_smul_subset_right (fun _ : AdelicGroupPoints F G => c) k
    refine ⟨c • k, testFunction_smul hk c, hs.trans hks, ?_⟩
    intro f hf hfi b
    rw [map_smul, LinearMap.smul_apply, heq]
    apply Subtype.ext
    funext x
    change c * rightConvolution F G k f (pair F G x b) =
      rightConvolution F G (c • k) f (pair F G x b)
    simp only [rightConvolution, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  | hgen X a ha =>
    obtain ⟨k, hk, hks, heq⟩ := ha
    obtain ⟨hk', hsupp⟩ := rightConvolutionKernelDerivative_isTestFunction hsmooth X hk
    refine ⟨rightConvolutionKernelDerivative hsmooth X k, hk', hsupp.trans hks, ?_⟩
    intro f hf hfi b
    rw [map_mul, Module.End.mul_apply, heq]
    change plotSmoothEnvelopingAction F G hsmooth hcalc
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) (S k f hk hf hfi b) = _
    rw [plotSmoothEnvelopingAction_real_generator]
    apply Subtype.ext
    funext x
    exact (adelicRightConvolutionDifferentiation F G d hsmooth k f hk hf hfi).2.2 X x b

end Langlands.Global.AdelicGroupPoints
