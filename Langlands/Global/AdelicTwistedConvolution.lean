import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Global.AdelicConvolutionFiniteModel
import Langlands.Global.AdelicEisensteinRightTranslation
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.EisensteinEvaluationMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-! # Holomorphic convolution on the Iwasawa twists -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis.SeveralComplex

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G

/-- Twisting by the nonvanishing height power is an equivalence on continuous functions. -/
def IsIwasawaCompact.continuousParameterTwist (lam : ComplexCharacterParameter F P) :
    C(A, ℂ) ≃ₗ[ℂ] C(A, ℂ) where
  toFun f := ⟨hK.parameterTwist f lam, hK.continuous_parameterTwist f.continuous lam⟩
  invFun f := ⟨fun x => f x / hK.heightPower lam x,
    f.continuous.div (hK.continuous_heightPower lam) (hK.heightPower_ne_zero lam)⟩
  left_inv f := by
    ext x
    exact mul_div_cancel_right₀ (f x) (hK.heightPower_ne_zero lam x)
  right_inv f := by
    ext x
    exact div_mul_cancel₀ (f x) (hK.heightPower_ne_zero lam x)
  map_add' f g := by
    ext x
    exact add_mul (f x) (g x) (hK.heightPower lam x)
  map_smul' c f := by
    ext x
    exact mul_assoc c (f x) (hK.heightPower lam x)

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- At a fixed point, the Iwasawa height power is entire in linear coordinates. -/
theorem IsIwasawaCompact.differentiable_heightPower {n : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (x : A) :
    Differentiable ℂ (fun s => hK.heightPower (e s) x) :=
  (((complexParameterPairing F P).flip (hK.height x)).comp e
    |>.toContinuousLinearMap.differentiable).cexp

variable [LocallyOfFiniteType G.X.hom]

/-- Pointwise convolution of an Iwasawa twist by a compactly supported continuous kernel
is entire in the twist parameter. -/
theorem IsIwasawaCompact.differentiable_rightConvolution_parameterTwist {n : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) {h f : A → ℂ}
    (hh : Continuous h) (hcomp : HasCompactSupport h) (hf : Continuous f) (x : A) :
    Differentiable ℂ (fun s => rightConvolution F G h (hK.parameterTwist f (e s)) x) := by
  let measure : Measure A := Measure.haar
  let integrand (s : Fin n → ℂ) (g : A) := h g * (f (x * g) * hK.heightPower (e s) (x * g))
  have hcont : Continuous (fun z : (Fin n → ℂ) × A => integrand z.1 z.2) := by
    have hmul' : Continuous (fun z : (Fin n → ℂ) × A => x * z.2) :=
      continuous_const.mul continuous_snd
    have hpow : Continuous (fun z : (Fin n → ℂ) × A => hK.heightPower (e z.1) (x * z.2)) :=
      Complex.continuous_exp.comp ((continuous_complexParameterPairing_coordinates e).comp
        (continuous_fst.prodMk (hK.continuous_height.comp hmul')))
    exact (hh.comp continuous_snd).mul ((hf.comp hmul').mul hpow)
  have hdiff (g : A) : Differentiable ℂ (fun s => integrand s g) :=
    (differentiable_const _).mul ((differentiable_const _).mul
      (hK.differentiable_heightPower e (x * g)))
  let ν := measure.restrict (tsupport h)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hcomp.isCompact.measure_lt_top.ne
  have hd : DifferentiableOn ℂ (fun s => ∫ g, integrand s g ∂ν) Set.univ := by
    refine differentiableOn_integral_of_bounded ν integrand isOpen_univ
      (fun g => (hdiff g).differentiableOn) (fun s _ => ?_) (fun S _ hS => ?_)
    · exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · obtain ⟨M, hM⟩ := (hS.prod hcomp.isCompact).exists_bound_of_continuousOn hcont.continuousOn
      refine ⟨max 0 M, fun s hs g => ?_⟩
      by_cases hg : g ∈ tsupport h
      · exact (hM (s, g) ⟨hs, hg⟩).trans (le_max_right _ _)
      · simp only [integrand, image_eq_zero_of_notMem_tsupport hg, zero_mul, norm_zero, le_max_iff,
          le_refl, true_or]
  have heq : (fun s => ∫ g, integrand s g ∂ν) =
      fun s => rightConvolution F G h (hK.parameterTwist f (e s)) x := by
    funext s
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro g hg
    simp [integrand, image_eq_zero_of_notMem_tsupport hg]
  rwa [heq, differentiableOn_univ] at hd

/-- Transport the convolution operator to the fixed untwisted space of continuous functions. -/
def IsIwasawaCompact.twistedConvolutionEnd {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F P) : Module.End ℂ C(A, ℂ) :=
  (hK.continuousParameterTwist lam).symm.toLinearMap.comp
    ((rightConvolutionEnd hsmooth hh).comp (hK.continuousParameterTwist lam).toLinearMap)

@[simp]
theorem IsIwasawaCompact.twistedConvolutionEnd_apply {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F P)
    (f : C(A, ℂ)) (x : A) :
    hK.twistedConvolutionEnd hsmooth hh lam f x =
      rightConvolution F G h (hK.parameterTwist f lam) x / hK.heightPower lam x := rfl

/-- A single finite-dimensional space stable under the transported convolution operators
supplies the convolution equations for the Iwasawa twists, provided the operator on that
space is injective at the base parameter. -/
theorem IsIwasawaCompact.hasConvolutionEquationAt_parameterTwist_of_finiteDimensional {d n : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (hR : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) h)
    (hL : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
      (fun x => h x⁻¹))
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ)
    (f : C(A, ℂ)) (S : Submodule ℂ C(A, ℂ)) [FiniteDimensional ℂ S] (hf : f ∈ S)
    (hS : ∀ s, ∀ v ∈ S, hK.twistedConvolutionEnd hsmooth hh (e s) v ∈ S)
    (hinj : Function.Injective ((hK.twistedConvolutionEnd hsmooth hh (e s₀)).restrict (hS s₀))) :
    HasConvolutionEquationAt (K.comap (ofInfinite F G).toMonoidHom)
      (fun s => hK.parameterTwist f (e s)) s₀ := by
  let embed : S →ₗ[ℂ] (A → ℂ) := (ContinuousMap.coeFnLinearMap ℂ).comp S.subtype
  have hembed : Function.Injective embed := by
    intro v w hvw
    apply S.injective_subtype
    ext x
    exact congrFun hvw x
  obtain ⟨nodes, coord, hcoord⟩ :=
    EisensteinJet.exists_evaluationEquiv (𝕜 := ℂ) (V := S) (X := A) embed hembed
  let L := rightConvolutionEnd hsmooth hh
  let twist (s : Fin n → ℂ) := hK.continuousParameterTwist (e s)
  let W (s : Fin n → ℂ) := S.map (twist s).toLinearMap
  let E (s : Fin n → ℂ) : S ≃ₗ[ℂ] W s := (twist s).submoduleMap S
  let D (s : Fin n → ℂ) := (hK.twistedConvolutionEnd hsmooth hh (e s)).restrict (hS s)
  let D' (s : Fin n → ℂ) :=
    coord.toLinearMap.comp ((D s).comp coord.symm.toLinearMap)
  let B (s : Fin n → ℂ) := (D' s).toMatrix'
  have hcoerce (s : Fin n → ℂ) (v : S) : (E s (D s v) : C(A, ℂ)) = L (E s v) := by
    change twist s ((twist s).symm (L (twist s v))) = L (twist s v)
    exact (twist s).apply_symm_apply _
  have hW (s : Fin n → ℂ) : ∀ v ∈ W s, L v ∈ W s := by
    intro v hv
    obtain ⟨w, hw⟩ := (E s).surjective ⟨v, hv⟩
    rw [← show (E s w : C(A, ℂ)) = v from congrArg Subtype.val hw, ← hcoerce]
    exact (E s (D s w)).property
  let q (s : Fin n → ℂ) := coord.toLinearMap.comp (E s).symm.toLinearMap
  refine hasConvolutionEquationAt_of_finiteModel hsmooth _ hh hR hL
    (fun s => twist s f) s₀ W (fun s => ⟨f, hf, rfl⟩) hW q
    (fun s => coord.injective.comp (E s).symm.injective) B ?_ ?_ ?_
  · intro i j
    let v : S := coord.symm (Pi.single j 1)
    have hentry (s : Fin n → ℂ) : B s i j = (D s v : C(A, ℂ)) (nodes i) := by
      simp only [B, LinearMap.toMatrix'_apply, D', LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact hcoord (D s v) i
    simp_rw [hentry]
    change Differentiable ℂ (fun s => hK.twistedConvolutionEnd hsmooth hh (e s)
      (v : C(A, ℂ)) (nodes i))
    simp only [IsIwasawaCompact.twistedConvolutionEnd_apply]
    simp only [div_eq_mul_inv]
    exact (hK.differentiable_rightConvolution_parameterTwist e hh.1.1 hh.2.1
      (v : C(A, ℂ)).continuous (nodes i)).mul
      ((hK.differentiable_heightPower e (nodes i)).inv
        (fun s => hK.heightPower_ne_zero (e s) (nodes i)))
  · rw [← LinearMap.det_toLin', ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
      LinearMap.ker_eq_bot]
    change Function.Injective ((D' s₀).toMatrix'.toLin')
    rw [Matrix.toLin'_toMatrix']
    exact coord.injective.comp (hinj.comp coord.symm.injective)
  · intro s v
    obtain ⟨w, rfl⟩ := (E s).surjective v
    have hmatch : L.restrict (hW s) (E s w) = E s (D s w) :=
      Subtype.ext (hcoerce s w).symm
    change q s (L.restrict (hW s) (E s w)) = (B s).toLin' (q s (E s w))
    rw [hmatch, show (B s).toLin' = D' s from Matrix.toLin'_toMatrix' _]
    simp [q, D']

end Langlands.Global.AdelicGroupPoints
