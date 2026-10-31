import Langlands.AbelianScheme.TrivialPullbackCharacterInjective
import Langlands.AbelianScheme.TrivialPullbackCharacterSurjective
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentEffectiveProof
import Langlands.AlgebraicGeometry.Picard.FieldIsogenyKernelDescentStatements

/-! # Classification of trivial field-isogeny pullbacks by the normalized character -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.Scheme.Modules

/-- Both descent statements give bijectivity of the normalized character over a field. -/
theorem fieldTrivialPullbackCharacterBijective_of_descent
    (hU : UnitCocycleDescentUniquenessStatement.{u})
    (hE : UnitCocycleDescentEffectiveStatement.{u}) :
    FieldTrivialPullbackCharacterBijectiveStatement.{u} := by
  intro k _ A B f hf T
  exact ⟨trivialPullbackCharacterInjective_of_uniqueness hU _ A B f hf T,
    trivialHomPullbackClassCharacter_surjective_of_effective f hE hf T⟩

/-- Over every base, the normalized character of trivial isogeny pullbacks is surjective. -/
theorem trivialHomPullbackClassCharacter_surjective {S : Scheme.{u}} {A B : AbelianScheme S}
    (f : A ⟶ B) (hf : IsIsogeny f) (T : Over S) :
    Function.Surjective
      (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A)) :=
  trivialHomPullbackClassCharacter_surjective_of_effective f unitCocycleDescentEffective hf T

/-- Over every base, the normalized character of trivial isogeny pullbacks is bijective. -/
theorem trivialHomPullbackClassCharacter_bijective {S : Scheme.{u}} {A B : AbelianScheme S}
    (f : A ⟶ B) (hf : IsIsogeny f) (T : Over S) :
    Function.Bijective
      (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A)) :=
  ⟨trivialPullbackCharacterInjective S A B f hf T,
    trivialHomPullbackClassCharacter_surjective f hf T⟩

/-- Over a field, the normalized character classifies trivial isogeny pullbacks. -/
theorem fieldTrivialPullbackCharacterBijective :
    FieldTrivialPullbackCharacterBijectiveStatement.{u} :=
  fun _ _ _ _ f hf T ↦ trivialHomPullbackClassCharacter_bijective f hf T

end Langlands.AbelianScheme
