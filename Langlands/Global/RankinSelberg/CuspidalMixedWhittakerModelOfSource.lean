import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerFunctional
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModel

/-! # The mixed Whittaker model for a compatible source embedding -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.OperatorDeterminantSlice
  Langlands.Global.ArchimedeanGL Langlands.Archimedean Langlands.Archimedean.MixedSmooth MeasureTheory

universe u v

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup
  regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

section SourceData

universe uV uX

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (σ : FiniteAdelicGL F n →* (E →L[ℂ] E))
  (π : ArchimedeanGL F n →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F n)
local notation "S" => Langlands.Archimedean.smoothVectors I π
local notation "W" => Vectors (A := ArchimedeanMatrix F n) σ π hcomm

/-- Use the computed functional with any mixed source map whose smooth
values agree with the compatible original embedding. The identities
of the three actions are stated on the underlying Hilbert space. -/
structure SmoothSourceWhittakerData
    (ρ : Representation ℂ (FiniteAdelicGL F n) V)
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (D : X → Module.End ℂ V) (ζ : X → ArchimedeanMatrix F n) (sourceNorm : V → ℝ)
    (j : V →ₗ[ℂ] S) (jM : V →ₗ[ℂ] W) : Prop where
  smoothValue : ∀ w, (jM w).val = j w
  injective : Function.Injective j
  norm_eq : ∀ w, sourceNorm w = ‖(j w).val‖
  unitary : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y
  denseSmooth : DenseRange (Subtype.val : S → E)
  finiteAction : ∀ d w, σ d (j w).val = (j (ρ d w)).val
  denseAtLevel : DenseFixedImages (A := ArchimedeanMatrix F n) ρ σ π j
  compactAction : ∀ (k : standardInfiniteCompact F n) (w : V),
      (j (κ k w)).val = π (archimedeanGLCoordinates F n k.val) (j w).val
  generator : ∀ (x : X) (w : V), (j (D x w)).val = lieDerivative I π (ζ x) (j w).val

end SourceData

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "S" => Langlands.Archimedean.smoothVectors I π
local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm

/-- The band estimate gives the Whittaker functional for the given
compatible mixed embedding. -/
theorem hasMixedWhittakerModel_of_smoothSource
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (hL2 : ∀ x : T.Space, MemLp (toQuotient F (r + 1) T.realization x) 2
      ((quotientHaarMeasure F (r + 1)).restrict (band F (r + 1))))
    (hbound : CuspidalWhittakerBandBound F T hL2 ψ)
    (j : T.Space →ₗ[ℂ] S) (jM : T.Space →ₗ[ℂ] W)
    (h : SmoothSourceWhittakerData σ π hcomm
      T.realization.finiteRepresentation T.realization.compactRepresentation
      (fun X => T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)))
      (realLieAlgebraToMatrix F (r + 1))
      (fun w => ‖toL2 F (r + 1) T.realization (quotientHaarMeasure F (r + 1)) hL2 w‖) j jM) :
    HasMixedWhittakerModel T ψ σ π hcomm jM := by
  have hfinite' (d : FiniteAdelicGL F (r + 1)) (w : T.Space) :
      finiteOnSmooth (A := ArchimedeanMatrix F (r + 1)) σ π hcomm d (j w) =
        j (T.realization.finiteRepresentation d w) :=
    Subtype.ext (h.finiteAction d w)
  let q := sourceToMixed T.realization.finiteRepresentation σ π hcomm j
    T.realization.finiteRepresentation_isSmooth hfinite'
  have hq : q.toLinearMap = jM := LinearMap.ext fun w => Subtype.ext (h.smoothValue w).symm
  have hm : HasMixedWhittakerModel T ψ σ π hcomm q.toLinearMap :=
    cuspidalMixedWhittakerFunctional T hL2 ψ σ π hcomm hψ hbound j h.injective h.norm_eq
      h.unitary h.denseSmooth hfinite' h.denseAtLevel
      (fun k w => Subtype.ext (h.compactAction k w)) (fun X w => Subtype.ext (h.generator X w))
  exact hq ▸ hm

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
