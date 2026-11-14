import Langlands.Geometry.Building.LangChamberReduction
import Langlands.GroupScheme.Rational.LangFixedOrbit

/-! # Finite-field quotient data for a semilinear chamber orbit -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)
  (κ Ω : Type v) [Field κ] [Fintype κ] [Field Ω]
  [Algebra κ Ω] [Algebra.IsAlgebraic κ Ω]
  (θ : rationalPoints G → rationalPoints G)
  (τ : B.ReducedBuilding → B.ReducedBuilding) (y : B.ReducedBuilding)

/-- A quotient of a point-fixing subgroup onto actual geometric points of a
connected reductive finite-field group, compatible with the specified group
twist and canonical Frobenius descent, together with one incident chamber orbit. -/
def HasFiniteFieldChamberQuotient : Prop :=
  ∃ R : GroupScheme (Spec (CommRingCat.of κ)), IsConnectedReductive R ∧
    ∃ (P : Subgroup (rationalPoints G))
      (q : P →* (Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap κ Ω)).obj R).X))
      (θP : P → P) (Y₀ : Set B.ReducedBuilding) (h : P),
      P ≤ B.fixer y ∧ Function.Surjective q ∧
      (∀ g : P, (θP g : rationalPoints G) = θ g) ∧
      (∀ g : P, q (θP g) =
        descentBasePoint (algebraBaseMap κ Ω)
          (galoisBaseMap κ Ω (FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω))
          (galoisBaseMap_over κ Ω (FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω))
          R (q g)) ∧
      B.HasChamberClosurePresentation Y₀ y ∧
      (∀ g : P, q g = 1 → ((g : rationalPoints G) • ·) '' Y₀ = Y₀) ∧
      τ '' Y₀ = ((h : rationalPoints G) • ·) '' Y₀

variable {B κ Ω θ τ y}

/-- Lang's theorem turns the supplied finite-field quotient data into a stable
chamber with the same specified closure point. -/
theorem HasFiniteFieldChamberQuotient.exists_stable_chamber [IsAlgClosed Ω]
    (hred : B.HasFiniteFieldChamberQuotient κ Ω θ τ y)
    (hsemi : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      τ (g • z) = θ g • τ z) :
    ∃ Y : Set B.ReducedBuilding,
      B.IsChamber Y ∧ τ '' Y = Y ∧ B.HasChamberClosurePresentation Y y := by
  obtain ⟨R, hR, P, q, θP, Y₀, h, hP, hq, hθ, hcompat, hY₀, hker, hτ⟩ := hred
  let : Smooth R.X.hom := hR.smooth
  let : IsAffineHom R.X.hom := hR.isAffineHom
  let : ConnectedSpace R.X.left := hR.connectedSpace
  exact B.exists_stable_chamber_of_quotient_lang P q hq θP _ τ hcompat
    (fun g z => by rw [hsemi, hθ])
    (langSurjective_descentBasePoint κ Ω R) y hP Y₀ hY₀ hker h hτ

end Langlands.Geometry.Building.IntegerValuationBuildingData
