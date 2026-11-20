import Langlands.Galois.FrobeniusLift
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Frobenius

/-! # Restriction of local inertia and Frobenius to finite abelian subfields -/

noncomputable section

universe uK

namespace Langlands.GaloisRepresentation

open Langlands.Global

variable {K : Type uK} [Field K] [NumberField K]

/-- The absolute Galois map for the actual completion, as used in
`LambdaAdicCharacter.atFinitePlace`. -/
abbrev localToGlobalGalois (v : FinitePlace K) :
    LocalGroup v →ₜ* Field.absoluteGaloisGroup K :=
  Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)

/-- Restriction to an actual finite Galois subfield with its Krull topology. -/
def finiteGaloisRestriction (E : IntermediateField K (AlgebraicClosure K)) [IsGalois K E] :
    Field.absoluteGaloisGroup K →ₜ* (E ≃ₐ[K] E) where
  toMonoidHom := AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) E
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E

/-- At an unramified place of a finite abelian subfield, the actual
restriction kills local inertia. The inverse of a geometric lift restricts
to arithmetic Frobenius at the chosen prime above the place. -/
def FiniteUnramifiedGaloisRestrictionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsGalois K E],
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : NumberField E := NumberField.of_module_finite K E
    ∀ (v : FinitePlace K) (w : FinitePlace E),
      w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal →
      (∀ i : localInertia v, finiteGaloisRestriction E (localToGlobalGalois v i.val) = 1) ∧
      ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
        (NumberField.RingOfIntegers.mapAlgHom
          (finiteGaloisRestriction E (localToGlobalGalois v g⁻¹))).IsArithFrobAt w.asIdeal

end Langlands.GaloisRepresentation
