import Langlands.Global.AdelicFiniteConvolutionInvertibility
import Langlands.Global.AdelicLocalizedConvolutionApproximation

/-! # Finite models of localized transported convolution -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

section Twists

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

local notation "J" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K

/-- A finite-dimensional space stable under localized, transported double averages
gives the uniform equation. At the base parameter, the compact approximation
uses kernels supported over the prescribed open finite subgroup. -/
theorem IsIwasawaCompact.hasConvolutionEquationAt_of_localized_averaged_stability {d n : ℕ}
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
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hStable : ∀ (h : A → ℂ) (hh : IsAdelicTestFunction F G h), HasFiniteProjectionSupport L h →
      ∀ (s : Fin n → ℂ) v, v ∈ S →
      hK.twistedConvolutionEnd hsmooth
        (isAdelicTestFunction_leftCompactKernelAverage measure hsmooth a
          (isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh)) (e s) v ∈ S) :
    HasConvolutionEquationAt J (fun s => hK.parameterTwist f (e s)) s₀ := by
  let twist := hK.continuousParameterTwist (e s₀)
  let W := S.map twist.toLinearMap
  let equivalence : S ≃ₗ[ℂ] W := twist.submoduleMap S
  let filtered (h : A → ℂ) :=
    leftCompactKernelAverage measure a (rightCompactKernelAverage measure b h)
  let kernels (g : A → ℂ) := ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ HasFiniteProjectionSupport L h ∧ filtered h = g
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
    obtain ⟨h, hh, hSupp, rfl⟩ := hker
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨hK.twistedConvolutionEnd hsmooth (test_of_filtered h hh) (e s₀) u,
      hStable h hh hSupp s₀ u hu, hconjugate h hh u⟩
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
    obtain ⟨h, hh, hSupp, hclose⟩ :=
      exists_averaged_rightConvolution_approximation_of_finite_support measure hsmooth values a b
        ha' hb' L hL hC hε
    exact ⟨filtered h, test_of_filtered h hh, ⟨h, hh, hSupp, rfl⟩, hclose⟩
  let : FiniteDimensional ℂ W := inferInstanceAs (FiniteDimensional ℂ (S.map twist.toLinearMap))
  obtain ⟨g, hg, hker, hinj⟩ :=
    exists_injective_rightConvolution_of_approximation hsmooth W kernels happrox hpreserve
  obtain ⟨h, hh, hSupp, rfl⟩ := hker
  have hrighttest := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  let gRight : C(A, ℂ) := ⟨rightCompactKernelAverage measure b h, hrighttest.1.1⟩
  have hright : IsInfiniteSubgroupFiniteFunction F G J (filtered h) :=
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage measure a gRight
      (isInfiniteSubgroupFiniteFunction_rightCompactKernelAverage measure b ⟨h, hh.1.1⟩ hbFinite)
  have hleft : IsInfiniteSubgroupFiniteFunction F G J (fun x => filtered h x⁻¹) :=
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage_inv measure a gRight haFinite
  refine hK.hasConvolutionEquationAt_parameterTwist_of_finiteDimensional hsmooth
    (test_of_filtered h hh) hright hleft e s₀ f S hf (hStable h hh hSupp) ?_
  let U := (rightConvolutionEnd hsmooth hg).restrict
    (hpreserve (filtered h) hg ⟨h, hh, hSupp, rfl⟩)
  let V := (hK.twistedConvolutionEnd hsmooth (test_of_filtered h hh) (e s₀)).restrict
    (hStable h hh hSupp s₀)
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
