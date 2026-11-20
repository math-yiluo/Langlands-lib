import Langlands.Galois.FiniteUnramifiedGaloisRestriction
import Langlands.Global.Arithmetic.FiniteArtinUnramifiedCriterion

/-! # Geometrically normalized lifts of finite idele-class characters -/

noncomputable section

universe uK uA

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped Valued

variable {K : Type uK} [Field K] [NumberField K]
variable {A : Type uA} [Monoid A] [TopologicalSpace A]

/-- Triviality of an idele-class character on the embedded local integral units. -/
def IsTrivialOnLocalUnits (ξ : IdeleClasses K →ₜ* A) (v : FinitePlace K) : Prop :=
  ∀ a : (FiniteCompletion K v)ˣ,
    a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units →
    ξ (finiteClassInclusion K v a) = 1

/-- At every place outside `S`, the actual local restriction is trivial on
inertia and evaluates at every geometric Frobenius lift as the idele-class
character does at a uniformizer. -/
def MatchesGeometricArtinOutside (S : Finset (FinitePlace K))
    (ξ : IdeleClasses K →ₜ* A) (ψ : Field.absoluteGaloisGroup K →ₜ* A) : Prop :=
  ∀ v ∉ S,
    (∀ i : localInertia v, ψ (localToGlobalGalois v i.val) = 1) ∧
    ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
      ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
        ψ (localToGlobalGalois v g) = ξ (finiteClassInclusion K v π)

/-- Finite abelian coefficient characters have a unique geometrically
normalized lift with the indicated set of good places. -/
def FiniteGeometricArtinLifting : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (A : Type uA) [CommGroup A] [Finite A],
    letI : TopologicalSpace A := ⊥
    ∀ (ξ : IdeleClasses K →ₜ* A) (S : Finset (FinitePlace K)),
      (∀ v ∉ S, IsTrivialOnLocalUnits ξ v) →
      ∃! ψ : Field.absoluteGaloisGroup K →ₜ* A, MatchesGeometricArtinOutside S ξ ψ

/-- The finite lift uses normalized class-field existence on the actual
kernel, the local-unit criterion there, and the comparison with actual
local Galois restriction. -/
def FiniteHeckeAvatarLiftStatement : Prop :=
  FiniteAbelianClassFieldExistenceStatement.{uK} →
  FiniteArtinUnramifiedCriterionStatement.{uK, uK} →
  FiniteUnramifiedGaloisRestrictionStatement.{uK} →
  FiniteGeometricArtinLifting.{uK, uA}

end Langlands.GaloisRepresentation
