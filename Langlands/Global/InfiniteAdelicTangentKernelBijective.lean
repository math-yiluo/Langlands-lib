import Langlands.Global.InfiniteAdelicTangentKernel
import Langlands.Global.InfiniteAdelicChartFormula
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Identity tangent vectors of `G(F_∞)` correspond bijectively to dual-number kernel points

A regular function of the base change of an affine scheme, evaluated at base-changed points, is
a finite sum of constant multiples of original regular functions. Hence a tangent vector at the
identity of `G(F_∞)` along which every global regular function has zero derivative also kills
the regular functions of every base change `G_{F_v}`, in particular the numerators and
denominators of the regular charts of the Library's atlas, and is zero. So `tangentKernel` is
injective; it is real-linear between spaces of the same real dimension, hence bijective. -/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology Langlands.Geometry.Manifold.ZeroDirectionalDerivative

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A]
  [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
  (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left] [TopologicalSpace A]

/-- A regular function of the base change, at base-changed points, is the tensor-extended
evaluation of one fixed element of `D ⊗[C] O(X)`. -/
theorem exists_tensor_baseChange_evaluation
    (b : AffineCoordinateRing D (ringBaseChange C D X)) :
    ∃ t : D ⊗[C] AffineCoordinateRing C X, ∀ p : RingPoint C X A,
      affineSchemePointEquiv D (ringBaseChange C D X) A (ringPointBaseChangeEquiv C D A X p) b =
        AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A
          (affineSchemePointEquiv C X A p) t := by
  let T := D ⊗[C] AffineCoordinateRing C X
  let e := ringBaseChangeAffineOverIso C D X
  let a' := (affineCoordinateAlgEquiv D e).symm b
  refine ⟨spectrumCoordinateAlgEquiv D T a', fun p => ?_⟩
  let q := ringPointBaseChangeEquiv C D A X p
  have hs := congrArg (fun r : AlgPoint D (AffineCoordinateRing D (ringTest D T)) A => r a')
    (affineSchemePointEquiv_spectrum D A T (q ≫ e.hom))
  have hn := congrArg (fun r : AlgPoint D (AffineCoordinateRing D (ringTest D T)) A => r a')
    (affineSchemePointEquiv_natural D A e.hom q)
  have he : affineRingPointEquiv D T A (q ≫ e.hom) (spectrumCoordinateAlgEquiv D T a') =
      affineSchemePointEquiv D (ringBaseChange C D X) A q
        (affineCoordinateAlgEquiv D e a') := hs.symm.trans hn
  rw [AlgEquiv.apply_symm_apply] at he
  rw [← he]
  exact congrArg (fun r : AlgPoint D T A => r (spectrumCoordinateAlgEquiv D T a'))
    (ringPointBaseChange_tensor_coordinates C D A X p)

variable {B : Type v} [NormedCommRing B] [NormedAlgebra ℝ B] (c : A →+* B)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- If every original regular function has zero derivative along `Y` at base points, so has
every regular function of the base change at the base-changed points. -/
theorem zeroDeriv_ringPoint_baseChange {x : M} {Y : TangentSpace I x} (p : M → RingPoint C X A)
    (hp : ∀ a : AffineCoordinateRing C X,
      ZeroDeriv Y (fun y => c (affineSchemePointEquiv C X A (p y) a)))
    (b : AffineCoordinateRing D (ringBaseChange C D X)) :
    ZeroDeriv Y (fun y => c (affineSchemePointEquiv D (ringBaseChange C D X) A
      (ringPointBaseChangeEquiv C D A X (p y)) b)) := by
  obtain ⟨t, ht⟩ := exists_tensor_baseChange_evaluation C D A X b
  simp_rw [ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | tmul d a =>
      have h := (zeroDeriv_const (X := Y) (c (algebraMap D A d))).mul (hp a)
      refine h.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [AlgPoint.baseChangeEquiv_tmul, map_mul]
  | add t t' ht ht' =>
      have h := ht.add ht'
      refine h.congr (Filter.Eventually.of_forall fun y => ?_)
      change _ = c ((AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A
        (affineSchemePointEquiv C X A (p y))).toAlgHom (t + t'))
      rw [map_add, map_add]
      rfl

end Langlands.AlgebraicGeometry.PointManifold

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.GroupScheme.General
open Langlands.AlgebraicGeometry.PointTopology Langlands.AlgebraicGeometry.PointManifold
open Langlands.AlgebraicGeometry.PointManifold.General
open Langlands.Geometry.Manifold.ZeroDirectionalDerivative

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- A tangent vector at `1` of `G(F_∞)` along which every regular function of every base change
`G_{F_v}`, evaluated at the `v`-component, has zero derivative is zero. -/
theorem eq_zero_of_zeroDeriv_baseChangeEvaluation :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ X : TangentSpace 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G),
      (∀ (v : InfinitePlace F)
          (b : Γ((InfinitePlaceGroupPoints.completionBaseChange F G v).X.left, ⊤)),
        ZeroDeriv X (fun g => regularEvaluation
          (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) b)) →
      X = 0 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  intro X hreg
  have hcomp (v : InfinitePlace F) (k : Fin d) :
      ZeroDeriv X (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)
        g v k) := by
    let c := placeRegularChart F G hsmooth v (atPlace F G v 1)
    have hmem1 : affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v 1) ∈
        c.homeomorph.source :=
      (smoothAffineRegularAtlas (affineBaseChange_smooth F v.Completion G hsmooth)).mem_source _
    let L : smoothModel F d →L[ℝ] v.Completion :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => v.Completion) k).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun w : InfinitePlace F => Fin d → w.Completion) v)
    have hsmoothc : MDifferentiableAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion)
        (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G) g v k)
        1 :=
      ((L.contDiff (n := ∞)).contMDiff.contMDiffAt.comp _
        (contMDiffAt_extChartAt (n := ∞))).mdifferentiableAt (by simp)
    have heq : (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)
          g v k) =ᶠ[nhds 1] fun g =>
        regularEvaluation
            (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g))
              (c.numerator k) /
          regularEvaluation
            (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g))
              (c.denominator k) := by
      filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, smoothModel F d))
        (1 : InfiniteAdelicGroupPoints F G)] with g hg
      rw [extChartAt_apply]
      exact c.apply_eq _ ((mem_extChartAt_source_iff F G hsmooth 1 g).mp hg v) k
    have hq := (hreg v (c.numerator k)).div (hreg v (c.denominator k))
      (c.denominator_ne_zero _ hmem1 k) (hsmoothc.congr_of_eventuallyEq heq.symm)
    exact hq.congr heq.symm
  have hchart : HasMFDerivAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d)
      (extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)) 1
      (ContinuousLinearMap.id ℝ (smoothModel F d)) := by
    have h := ((contMDiffAt_extChartAt (I := 𝓘(ℝ, smoothModel F d)) (n := ∞)
      (x := (1 : InfiniteAdelicGroupPoints F G))).mdifferentiableAt (by simp)).hasMFDerivAt
    rw [mfderiv_extChartAt_self] at h
    exact h
  have hvk (v : InfinitePlace F) (k : Fin d) : (X : smoothModel F d) v k = 0 := by
    let L : smoothModel F d →L[ℝ] v.Completion :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => v.Completion) k).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun w : InfinitePlace F => Fin d → w.Completion) v)
    obtain ⟨h', hh', hX'⟩ := hcomp v k
    have hL := (L.hasMFDerivAt (x := extChartAt 𝓘(ℝ, smoothModel F d)
      (1 : InfiniteAdelicGroupPoints F G) 1)).comp (1 : InfiniteAdelicGroupPoints F G) hchart
    have huniq := hL.mfderiv.symm.trans hh'.mfderiv
    have h1 := congrArg (fun T => T X) huniq
    change L X = h' X at h1
    rw [hX'] at h1
    exact h1
  funext v k
  exact hvk v k

/-- Along a tangent vector killing all global regular functions, every regular function of the
base change `G_{F_v}` at the `v`-component has zero derivative. -/
theorem zeroDeriv_baseChangeEvaluation
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (hX : ∀ a : AffineCoordinateRing F G.X, regularDerivative F hsmooth X a = 0)
    (v : InfinitePlace F)
    (b : Γ((InfinitePlaceGroupPoints.completionBaseChange F G v).X.left, ⊤)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ZeroDeriv X (fun g => regularEvaluation
      (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) b) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  have hp (a : AffineCoordinateRing F G.X) :
      ZeroDeriv X (fun y => (RingHom.id v.Completion)
        (affineSchemePointEquiv F G.X v.Completion (atPlace F G v y) a)) := by
    have hd := ((contMDiff_placeValue F hsmooth v a) 1).mdifferentiableAt (by simp)
    have h0 : ZeroDeriv X (placeValue F v a) := ⟨_, hd.hasMFDerivAt, congrFun (hX a) v⟩
    refine h0.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (atPlace_evaluation F G y a v).symm.trans
      (G.affineSchemePointEquiv_evaluation (CommAlgCat.of F v.Completion) (atPlace F G v y) a).symm
  have h := zeroDeriv_ringPoint_baseChange F v.Completion v.Completion G.X
    (RingHom.id v.Completion) (fun y => atPlace F G v y) hp b
  refine h.congr (Filter.Eventually.of_forall fun g => ?_)
  show affineSchemePointEquiv v.Completion (ringBaseChange F v.Completion G.X) v.Completion
      (ringPointBaseChangeEquiv F v.Completion v.Completion G.X (atPlace F G v g)) b =
    regularEvaluation (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) b
  rw [regularEvaluation_affineBaseChangePointHomeomorph,
    affinePointsBaseChangeMulEquiv_eq_ringPoint]
  exact affineSchemePointEquiv_evaluation
    (InfinitePlaceGroupPoints.completionBaseChange F G v)
    (CommAlgCat.of v.Completion v.Completion) _ b

/-- The dual-number kernel element `tangentKernel X` determines `X`. -/
theorem tangentKernel_injective : Function.Injective (tangentKernel F hsmooth) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro X Y hXY
  have hD (a : AffineCoordinateRing F G.X) : regularDerivative F hsmooth (X - Y) a = 0 := by
    have h1 := kernelDerivationEquiv_tangentKernel F hsmooth X a
    have h2 := kernelDerivationEquiv_tangentKernel F hsmooth Y a
    rw [hXY] at h1
    have h3 := regularDerivative_add_left F hsmooth (X - Y) Y a
    rw [sub_add_cancel] at h3
    rw [← h1, h2] at h3
    exact add_eq_right.mp h3.symm
  have h0 := eq_zero_of_zeroDeriv_baseChangeEvaluation F hsmooth (X - Y)
    (fun v b => zeroDeriv_baseChangeEvaluation F hsmooth (X - Y) hD v b)
  exact sub_eq_zero.mp h0

/-- Every element of the dual-number kernel of `G` over `F_∞` is `tangentKernel X` for an
identity tangent vector `X`: both sides have real dimension `d · Σ_v [F_v : ℝ]`. -/
theorem tangentKernel_surjective : Function.Surjective (tangentKernel F hsmooth) := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : SmoothOfRelativeDimension d G.X.hom := hsmooth
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  have hdim : Module.finrank F (Additive (lieKernel G F)) = d :=
    Lie.dimension_eq_of_smoothOfRelativeDimension G hsmooth
  let b : Module.Basis (Fin d) F (Additive (lieKernel G F)) :=
    Module.finBasisOfFinrankEq F _ hdim
  let e : Additive (lieKernel G (InfiniteAdeleRing F)) ≃ₗ[InfiniteAdeleRing F]
      (Fin d → InfiniteAdeleRing F) :=
    (Lie.kernelScalarExtension G (InfiniteAdeleRing F)).symm.trans
      (b.baseChange (InfiniteAdeleRing F)).equivFun
  let Ψ : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ[ℝ]
      (Fin d → (v : InfinitePlace F) → v.Completion) :=
    { toFun := fun X => e (Additive.ofMul (tangentKernel F hsmooth X))
      map_add' := fun X Y => by
        change e (Additive.ofMul (tangentKernel F hsmooth (X + Y))) =
          e (Additive.ofMul (tangentKernel F hsmooth X)) +
            e (Additive.ofMul (tangentKernel F hsmooth Y))
        rw [tangentKernel_add, ofMul_mul, map_add]
      map_smul' := fun r X => by
        rw [RingHom.id_apply]
        funext i v
        change e (Additive.ofMul (tangentKernel F hsmooth (r • X))) i v =
          r • e (Additive.ofMul (tangentKernel F hsmooth X)) i v
        rw [tangentKernel_smul]
        change e (realAdele F r • Additive.ofMul (tangentKernel F hsmooth X)) i v = _
        rw [map_smul]
        change realAdele F r v * _ = _
        exact (RCLike.real_smul_eq_coe_mul (K := v.Completion) r _).symm }
  have hinj : Function.Injective Ψ := fun X Y h =>
    tangentKernel_injective F hsmooth (Additive.ofMul.injective (e.injective h))
  let c := (tangentSpaceCastModel 𝓘(ℝ, smoothModel F d)
    (1 : InfiniteAdelicGroupPoints F G)).toLinearEquiv
  have : FiniteDimensional ℝ
      (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :=
    c.symm.finiteDimensional
  have hfin : Module.finrank ℝ
      (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) =
      Module.finrank ℝ (Fin d → (v : InfinitePlace F) → v.Completion) := by
    rw [c.finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp_rw [Module.finrank_pi_fintype]
    exact Finset.sum_comm
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  intro x
  obtain ⟨X, hX⟩ := hsurj (e (Additive.ofMul x))
  exact ⟨X, Additive.ofMul.injective (e.injective hX)⟩

/-- `X ↦ tangentKernel X` is a bijection from the Lie algebra of `G(F_∞)` onto the dual-number
kernel of `G` over `F_∞`. -/
theorem tangentKernel_bijective : Function.Bijective (tangentKernel F hsmooth) :=
  ⟨tangentKernel_injective F hsmooth, tangentKernel_surjective F hsmooth⟩

end Langlands.Global.InfiniteAdelicGroupPoints
