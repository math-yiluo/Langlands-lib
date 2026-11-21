import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerExtensions

/-! # A derivative-continuous actual Whittaker functional on mixed smooth vectors -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField MeasureTheory
  Langlands.Archimedean Langlands.Archimedean.MixedSmooth

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  (hL2 : ∀ x : T.Space,
    MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))))
  (ψ : AddChar (Adeles F) ℂ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "ρ" => T.realization.finiteRepresentation
local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm

/-- The global scalar functional has derivative continuity at each finite
level and the actual adelic generic character. -/
def IsMixedWhittakerFunctional (ℓ : W →ₗ[ℂ] ℂ) : Prop :=
  IsContinuousAtEachLevel (A := ArchimedeanMatrix F (r + 1)) σ π hcomm ℓ ∧
    ∀ (z : unipotentAdelic F (r + 1)) (w : W),
      ℓ (MixedSmooth.finiteRepresentation σ π hcomm (finPart F (r + 1) z.val)
        (MixedSmooth.archimedeanRepresentation σ π hcomm (archPart F (r + 1) z.val) w)) =
        (genericCharacter F r ψ (fun _ => 1) z : ℂ) * ℓ w

/-- An actual band bound and the specified compatible smooth action yield
one global functional computing all translated Whittaker values. -/
def CuspidalMixedWhittakerFunctionalStatement : Prop :=
  let model := I
  let S := Langlands.Archimedean.smoothVectors model π
  let τ := finiteOnSmooth (A := ArchimedeanMatrix F (r + 1)) σ π hcomm
  ∀ (_ : IsStandardAdditiveCharacter F ψ) (_ : CuspidalWhittakerBandBound F T hL2 ψ)
    (j : T.Space →ₗ[ℂ] S) (_ : Function.Injective j)
    (_ : ∀ v : T.Space,
      ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
        (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2 v‖ = ‖(j v).val‖)
    (_ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (_ : DenseRange (Subtype.val : S → E))
    (hj : ∀ a v, τ a (j v) = j (ρ a v))
    (_ : DenseFixedImages (A := ArchimedeanMatrix F (r + 1)) ρ σ π j)
    (_ : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation model π (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (_ : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative model π (realLieAlgebraToMatrix F (r + 1) X) (j w)),
    ∃ ℓ : W →ₗ[ℂ] ℂ, IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ ∧
      (∀ (v : T.Space) (a : ArchimedeanGL F (r + 1)) (d : FiniteAdelicGL F (r + 1)),
        ℓ (MixedSmooth.finiteRepresentation σ π hcomm d
          (MixedSmooth.archimedeanRepresentation σ π hcomm a
            (sourceToMixed ρ σ π hcomm j T.realization.finiteRepresentation_isSmooth hj v))) =
          cuspWhittaker F T ψ v (adelicPoint F (r + 1) a d)) ∧
      (∀ v : T.Space, v ≠ 0 → ℓ ≠ 0)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
