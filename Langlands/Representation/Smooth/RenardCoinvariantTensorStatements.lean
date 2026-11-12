import Langlands.Representation.Hecke.NondegenerateModuleFunctor
import Langlands.Algebra.NonUnitalModuleTensor
import Langlands.Representation.Category.Twist
import Mathlib.RepresentationTheory.Coinvariants

/-! # Coinvariants of tensor products and the Hecke tensor product (Renard III.1.15)

For smooth representations `π₁`, `π₂` of a t.d. group `G`, the coinvariants `(V₁ ⊗ V₂)_G`
identify with `V₁ ⊗_{H(G)} V₂`, where `V₁` is a right `H(G)`-module through the anti-involution
`T ↦ Ť`; taking coinvariants of the associativity of `⊗` gives
`(V₁ ⊗ V₂) ⊗_{H(G)} V₃ ≃ V₁ ⊗_{H(G)} (V₂ ⊗ V₃)` (III.1.15.1). The tensor product of smooth
representations, used to define the functor `• ⊗ V` of III.1.15, is smooth. Twisting by a
one-dimensional smooth representation `ℂ_ω` is an equivalence with inverse `• ⊗ ℂ_ω⁻¹`, adjoint
to it on both sides (III.1.15, Remark 3).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory TensorProduct MulOpposite

namespace Langlands.Renard.Smooth

open Langlands.Hecke Langlands.Algebra

/-- A right action of the Hecke algebra on the carrier of a smooth representation `π` is the
action of the anti-involution `T ↦ Ť`: for `T = f μ`, the operator `π(Ť)` is
`v ↦ ∫ f(g) π(g⁻¹) v dμ(g)`, written as the integrated action of the inverted test function
`g ↦ f(g⁻¹)` for the inverted measure `μ.inv`. -/
def IsCheckRightAction {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    (M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V) : Prop :=
  ∀ (f : HeckeAlgebra μ) (x : V),
    (letI := M; op f • x) =
      integratedAction μ.inv π hπ
        (TestFunction.inversion (HeckeAlgebra.toTestFunction μ f)) x

/-- Renard III.1.14–III.1.15: the tensor product of two smooth representations of `G` is
smooth, so that `• ⊗ V` is a functor from smooth representations to themselves. -/
def TensorProductSmoothStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G]
    (V₁ V₂ : Type v) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂),
    IsSmooth π₁ → IsSmooth π₂ → IsSmooth (Representation.tprod π₁ π₂)

/-- Renard III.1.15 (right module through `T ↦ Ť`): for every smooth `π`, the operators
`π(Ť)` form a right action of the Hecke algebra on its carrier. -/
def CheckRightActionExistsStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π),
    ∃ M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V, IsCheckRightAction μ π hπ M

/-- Renard III.1.15 (coinvariants): for smooth `π₁`, `π₂`, with `V₁` a right Hecke module
through `T ↦ Ť` and `V₂` a left Hecke module through the integrated action, the coinvariants
`(V₁ ⊗ V₂)_G` are isomorphic to `V₁ ⊗_{H(G)} V₂` by `[v₁ ⊗ v₂] ↦ v₁ ⊗ v₂`. -/
def CoinvariantHeckeTensorStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V₁ V₂ : Type v) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂)
    (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂)
    (M₁ : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V₁), IsCheckRightAction μ π₁ hπ₁ M₁ →
    letI := M₁
    letI := heckeNonUnitalModule μ π₂ hπ₂
    ∃ e : Representation.Coinvariants (Representation.tprod π₁ π₂) ≃+
        NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V₁ V₂,
      ∀ (x₁ : V₁) (x₂ : V₂),
        e (Representation.Coinvariants.mk (Representation.tprod π₁ π₂) (x₁ ⊗ₜ x₂)) =
          NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V₁ V₂ x₁ x₂

/-- Renard (III.1.15.1): for smooth `π₁`, `π₂`, `π₃`,
`(V₁ ⊗ V₂) ⊗_{H(G)} V₃ ≃ V₁ ⊗_{H(G)} (V₂ ⊗ V₃)` by `(v₁ ⊗ v₂) ⊗ v₃ ↦ v₁ ⊗ (v₂ ⊗ v₃)`, the
right Hecke modules `V₁ ⊗ V₂` and `V₁` being given by `T ↦ Ť` and the left Hecke modules `V₃`
and `V₂ ⊗ V₃` by the integrated action. The smoothness of the two tensor products is
`TensorProductSmoothStatement`. -/
def HeckeTensorAssociativityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V₁ V₂ V₃ : Type v) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃]
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (π₃ : Representation ℂ G V₃)
    (hπ₁ : IsSmooth π₁) (hπ₃ : IsSmooth π₃)
    (h₁₂ : IsSmooth (Representation.tprod π₁ π₂)) (h₂₃ : IsSmooth (Representation.tprod π₂ π₃))
    (M₁₂ : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ (V₁ ⊗[ℂ] V₂))
    (M₁ : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V₁),
    IsCheckRightAction μ (Representation.tprod π₁ π₂) h₁₂ M₁₂ →
    IsCheckRightAction μ π₁ hπ₁ M₁ →
    ∃ e : (letI := M₁₂; letI := heckeNonUnitalModule μ π₃ hπ₃
          NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) (V₁ ⊗[ℂ] V₂) V₃) ≃+
        (letI := M₁; letI := heckeNonUnitalModule μ (Representation.tprod π₂ π₃) h₂₃
          NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V₁ (V₂ ⊗[ℂ] V₃)),
      ∀ (x₁ : V₁) (x₂ : V₂) (x₃ : V₃),
        e (letI := M₁₂; letI := heckeNonUnitalModule μ π₃ hπ₃
            NonUnitalModuleTensor.tmul (HeckeAlgebra μ) (V₁ ⊗[ℂ] V₂) V₃ (x₁ ⊗ₜ x₂) x₃) =
          (letI := M₁; letI := heckeNonUnitalModule μ (Representation.tprod π₂ π₃) h₂₃
            NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V₁ (V₂ ⊗[ℂ] V₃) x₁ (x₂ ⊗ₜ x₃))

/-- Renard III.1.15, Remark 3: for a one-dimensional smooth representation `(ω, ℂ_ω)`, that is a
character `ω : G → ℂˣ` with open kernel, the twist `• ⊗ ℂ_ω` and the twist `• ⊗ ℂ_ω⁻¹` are
mutually inverse up to natural isomorphism, and each is left adjoint to the other:
`Hom_G(V ⊗ ℂ_ω⁻¹, W) ≃ Hom_G(V, W ⊗ ℂ_ω)` naturally, and the same with `ω` and `ω⁻¹`
exchanged. -/
def TwistEquivalenceStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G]
    (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)) (hω' : IsOpen ((ω⁻¹).ker : Set G)),
    Nonempty (SmoothRep.twistFunctor.{0, u, v} ω hω ⋙ SmoothRep.twistFunctor ω⁻¹ hω' ≅
      𝟭 (SmoothRep.{0, u, v} ℂ G)) ∧
    Nonempty (SmoothRep.twistFunctor.{0, u, v} ω⁻¹ hω' ⋙ SmoothRep.twistFunctor ω hω ≅
      𝟭 (SmoothRep.{0, u, v} ℂ G)) ∧
    Nonempty (SmoothRep.twistFunctor.{0, u, v} ω⁻¹ hω' ⊣ SmoothRep.twistFunctor ω hω) ∧
    Nonempty (SmoothRep.twistFunctor.{0, u, v} ω hω ⊣ SmoothRep.twistFunctor ω⁻¹ hω')

/-- The five statements of this module. -/
def RenardCoinvariantTensorStatements.{u', v'} : Prop :=
  TensorProductSmoothStatement.{u', v'} ∧ CheckRightActionExistsStatement.{u', v'} ∧
    CoinvariantHeckeTensorStatement.{u', v'} ∧ HeckeTensorAssociativityStatement.{u', v'} ∧
    TwistEquivalenceStatement.{u', v'}

end Langlands.Renard.Smooth
