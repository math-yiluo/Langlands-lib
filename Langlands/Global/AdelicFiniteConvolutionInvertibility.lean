import Langlands.Global.AdelicBiFiniteConvolutionApproximation
import Langlands.Global.AdelicTwistedConvolution
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Invertible convolution on a finite-dimensional invariant space -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

/-- The indicated class of smooth test kernels approximates finite families in a subspace
uniformly on compact subsets of the adelic group. -/
def ConvolutionApproximates (kernels : (A → ℂ) → Prop) (S : Submodule ℂ C(A, ℂ)) : Prop :=
  ∀ {m : ℕ} (f : Fin m → S) {C : Set A}, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ kernels h ∧
      ∀ i x, x ∈ C → ‖rightConvolution F G h (f i : C(A, ℂ)) x - (f i : C(A, ℂ)) x‖ ≤ ε

/-- Within a class of kernels that preserves a finite-dimensional subspace and
approximates its finite families, some kernel acts injectively on the subspace. -/
theorem exists_injective_rightConvolution_of_approximation {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (S : Submodule ℂ C(A, ℂ)) [FiniteDimensional ℂ S]
    (kernels : (A → ℂ) → Prop) (happrox : ConvolutionApproximates kernels S)
    (hStable : ∀ (h : A → ℂ) (hh : IsAdelicTestFunction F G h), kernels h →
      ∀ v ∈ S, rightConvolutionEnd hsmooth hh v ∈ S) :
    ∃ (h : A → ℂ) (hh : IsAdelicTestFunction F G h) (hk : kernels h),
      Function.Injective ((rightConvolutionEnd hsmooth hh).restrict (hStable h hh hk)) := by
  let embed : S →ₗ[ℂ] (A → ℂ) := (ContinuousMap.coeFnLinearMap ℂ).comp S.subtype
  have hembed : Function.Injective embed := by
    intro v w hvw
    apply S.injective_subtype
    ext x
    exact congrFun hvw x
  obtain ⟨nodes, coord, hcoord⟩ :=
    EisensteinJet.exists_evaluationEquiv (𝕜 := ℂ) (V := S) (X := A) embed hembed
  let m := Module.finrank ℂ S
  let basis (j : Fin m) := coord.symm (Pi.single j 1)
  let Mat := Fin m → Fin m → ℂ
  let idMat : Mat := (1 : Matrix (Fin m) (Fin m) ℂ)
  let invertible : Set Mat := {M | (Matrix.of M).det ≠ 0}
  have hdet : Continuous (fun M : Mat => (Matrix.of M).det) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    exact continuous_finsetSum _ fun σ _ => continuous_const.mul
      (continuous_finsetProd _ fun j _ => (continuous_apply j).comp (continuous_apply (σ j)))
  have hOpen : IsOpen invertible := isClosed_singleton.isOpen_compl.preimage hdet
  have hOne : idMat ∈ invertible := by
    change (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0
    simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOpen idMat hOne
  obtain ⟨h, hh, hk, hClose⟩ := happrox basis (Set.finite_range nodes).isCompact (ε / 2)
    (half_pos hε)
  let D := (rightConvolutionEnd hsmooth hh).restrict (hStable h hh hk)
  let D' := coord.toLinearMap.comp (D.comp coord.symm.toLinearMap)
  let M := D'.toMatrix'
  have hentry (i j : Fin m) :
      M i j = rightConvolution F G h (basis j : C(A, ℂ)) (nodes i) := by
    simp only [M, D', LinearMap.toMatrix'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcoord (D (basis j)) i]
    rfl
  have hid (i j : Fin m) : idMat i j = (basis j : C(A, ℂ)) (nodes i) := by
    change idMat i j = embed (basis j) (nodes i)
    rw [← hcoord (basis j) i]
    simp only [basis, idMat, LinearEquiv.apply_symm_apply, Matrix.one_apply, Pi.single_apply]
  have hdist : dist (fun i j : Fin m => M i j) idMat ≤ ε / 2 := by
    refine (dist_pi_le_iff (half_pos hε).le).2 fun i =>
      (dist_pi_le_iff (half_pos hε).le).2 fun j => ?_
    rw [dist_eq_norm, hentry, hid]
    exact hClose j (nodes i) (Set.mem_range_self i)
  have hM : M.det ≠ 0 := hball (hdist.trans_lt (half_lt_self hε))
  refine ⟨h, hh, hk, ?_⟩
  intro v w hvw
  apply coord.injective
  apply Matrix.mulVec_injective_of_det_ne_zero hM
  rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  change D v = D w at hvw
  simp only [D', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hvw]

section Twists

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

local notation "J" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K

/-- A finite-dimensional space stable under the transported double averages
gives the uniform equation. Reproducing weights on the base fibre allow a
kernel with injective action there to be chosen by compact approximation. -/
theorem IsIwasawaCompact.hasConvolutionEquationAt_of_averaged_stability {d n : ℕ}
    (hK : IsIwasawaCompact p K) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    [CompactSpace J] [MeasurableSpace J] [BorelSpace J] (measure : Measure J) [measure.IsHaarMeasure]
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ)
    (f : C(A, ℂ)) (S : Submodule ℂ C(A, ℂ)) [FiniteDimensional ℂ S] (hf : f ∈ S)
    (a b : C(J, ℂ))
    (haFinite : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : J => fun t => a (k⁻¹ * t))))
    (hbFinite : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : J => fun t => b (k⁻¹ * t))))
    (ha : ∀ v : S, ∀ x,
      (∫ k, a k * hK.parameterTwist (v : C(A, ℂ)) (e s₀) (x * ofInfinite F G k.val) ∂measure) =
        hK.parameterTwist (v : C(A, ℂ)) (e s₀) x)
    (hb : ∀ v : S, ∀ x,
      (∫ k, b k * hK.parameterTwist (v : C(A, ℂ)) (e s₀)
        (x * (ofInfinite F G k.val)⁻¹) ∂measure) = hK.parameterTwist (v : C(A, ℂ)) (e s₀) x)
    (hStable : ∀ (h : A → ℂ) (hh : IsAdelicTestFunction F G h) (s : Fin n → ℂ) v, v ∈ S →
      hK.twistedConvolutionEnd hsmooth
        (isAdelicTestFunction_leftCompactKernelAverage measure hsmooth a
          (isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh)) (e s) v ∈ S) :
    HasConvolutionEquationAt J (fun s => hK.parameterTwist f (e s)) s₀ := by
  let twist := hK.continuousParameterTwist (e s₀)
  let W := S.map twist.toLinearMap
  let equivalence : S ≃ₗ[ℂ] W := twist.submoduleMap S
  let filtered (h : A → ℂ) :=
    leftCompactKernelAverage measure a (rightCompactKernelAverage measure b h)
  let kernels (g : A → ℂ) := ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ filtered h = g
  have test_of_filtered (h : A → ℂ) (hh : IsAdelicTestFunction F G h) :
      IsAdelicTestFunction F G (filtered h) :=
    isAdelicTestFunction_leftCompactKernelAverage measure hsmooth a
      (isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh)
  have hconjugate (h : A → ℂ) (hh : IsAdelicTestFunction F G h) (v : C(A, ℂ)) :
      twist (hK.twistedConvolutionEnd hsmooth (test_of_filtered h hh) (e s₀) v) =
        rightConvolutionEnd hsmooth (test_of_filtered h hh) (twist v) :=
    twist.apply_symm_apply _
  have hpreserve (g : A → ℂ) (hg : IsAdelicTestFunction F G g) (hker : kernels g)
      (v : C(A, ℂ)) (hv : v ∈ W) : rightConvolutionEnd hsmooth hg v ∈ W := by
    obtain ⟨h, hh, rfl⟩ := hker
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨hK.twistedConvolutionEnd hsmooth (test_of_filtered h hh) (e s₀) u,
      hStable h hh s₀ u hu, hconjugate h hh u⟩
  have happrox : ConvolutionApproximates kernels W := by
    intro m g C hC ε hε
    let values (i : Fin m) : C(A, ℂ) := g i
    have ha' (i : Fin m) (x : A) :
        (∫ k, a k * values i (x * ofInfinite F G k.val) ∂measure) = values i x := by
      obtain ⟨v, hv⟩ := equivalence.surjective (g i)
      have heq : values i = twist v := (congrArg Subtype.val hv).symm
      rw [heq]
      exact ha v x
    have hb' (i : Fin m) (x : A) :
        (∫ k, b k * values i (x * (ofInfinite F G k.val)⁻¹) ∂measure) = values i x := by
      obtain ⟨v, hv⟩ := equivalence.surjective (g i)
      have heq : values i = twist v := (congrArg Subtype.val hv).symm
      rw [heq]
      exact hb v x
    obtain ⟨h, hh, hclose⟩ :=
      exists_averaged_rightConvolution_approximation measure hsmooth values a b ha' hb' hC hε
    exact ⟨filtered h, test_of_filtered h hh, ⟨h, hh, rfl⟩, hclose⟩
  let : FiniteDimensional ℂ W := inferInstanceAs (FiniteDimensional ℂ (S.map twist.toLinearMap))
  obtain ⟨g, hg, hker, hinj⟩ :=
    exists_injective_rightConvolution_of_approximation hsmooth W kernels happrox hpreserve
  obtain ⟨h, hh, rfl⟩ := hker
  have hrighttest := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  let gRight : C(A, ℂ) := ⟨rightCompactKernelAverage measure b h, hrighttest.1.1⟩
  have hright : IsInfiniteSubgroupFiniteFunction F G J (filtered h) :=
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage measure a gRight
      (isInfiniteSubgroupFiniteFunction_rightCompactKernelAverage measure b ⟨h, hh.1.1⟩ hbFinite)
  have hleft : IsInfiniteSubgroupFiniteFunction F G J (fun x => filtered h x⁻¹) :=
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage_inv measure a gRight haFinite
  refine hK.hasConvolutionEquationAt_parameterTwist_of_finiteDimensional hsmooth
    (test_of_filtered h hh) hright hleft e s₀ f S hf (hStable h hh) ?_
  let U := (rightConvolutionEnd hsmooth hg).restrict
    (hpreserve (filtered h) hg ⟨h, hh, rfl⟩)
  let V := (hK.twistedConvolutionEnd hsmooth (test_of_filtered h hh) (e s₀)).restrict
    (hStable h hh s₀)
  have hrel (v : S) : equivalence (V v) = U (equivalence v) :=
    Subtype.ext (hconjugate h hh (v : C(A, ℂ)))
  intro v w hvw
  apply equivalence.injective
  apply hinj
  change U (equivalence v) = U (equivalence w)
  rw [← hrel, ← hrel]
  exact congrArg equivalence hvw

end Twists

end Langlands.Global.AdelicGroupPoints
