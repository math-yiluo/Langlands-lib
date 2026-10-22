import Langlands.Weil.Local.Assembly
import Langlands.WeilDeligne.Parameters

/-! # Actual local Weil representations and Weil–Deligne parameter classes -/

noncomputable section

universe u v

namespace Langlands.Weil.Local

open CategoryTheory

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- All finite-dimensional complex representations of the constructed local Weil group. -/
abbrev LocalWeilRepresentation :=
  FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)

/-- Genuine representation isomorphism classes on actual complex vector spaces. -/
abbrev LocalWeilClasses :=
  FiniteRepresentation.IsomorphismClasses.{0, u, v} ℂ (localWeilGroup F)

/-- Rank-indexed representation classes, with no semisimplicity condition. -/
abbrev LocalWeilClassesOfRank (n : ℕ) :=
  FiniteRepresentation.IsomorphismClassesOfRank.{0, u, v} ℂ (localWeilGroup F) n

/-- Usual-topology continuous representations; the complex topology is not discrete. -/
abbrev LocalContinuousWeilObjects :=
  FiniteRepresentation.ContinuousObjects.{u, v} (localWeilGroup F)

/-- The separate algebraic convention of open kernel on actual local inertia. -/
abbrev LocalOpenInertiaWeilObjects :=
  FiniteRepresentation.OpenInertiaObjects.{u, v} (localInertia F)

/-- Genuine classes of irreducible continuous representations in each rank. -/
abbrev LocalContinuousIrreducibleWeilClasses (n : ℕ) :=
  FiniteRepresentation.ContinuousIrreducibleClasses.{u, v} (localWeilGroup F) n

/-- Genuine semisimple representation classes in the open-inertia convention. -/
abbrev LocalSemisimpleWeilClasses (n : ℕ) :=
  FiniteRepresentation.OpenInertiaSemisimpleClasses.{u, v} (localInertia F) n

/-- Galois type means extension along the actual projection to the absolute Galois group. -/
def IsLocalGaloisType (A : LocalWeilRepresentation.{u, v} F) : Prop :=
  A.IsGaloisTypeAlong (localProjection F)

/-- All actual local Weil–Deligne pairs, including arbitrary nilpotent monodromy. -/
abbrev LocalWeilDeligneRepresentation :=
  WeilDeligneRepresentation.{0, u, v} ℂ (localWeilGroup F)
    (localNormCharacter F).toMonoidHom

/-- All genuine local pair classes of rank `n`, without imposing a parameter predicate. -/
abbrev LocalWeilDeligneClassesOfRank (n : ℕ) :=
  WeilDeligneRepresentation.IsomorphismClassesOfRank.{0, u, v} ℂ (localWeilGroup F)
    (localNormCharacter F).toMonoidHom n

/-- Local parameter objects with open inertia kernel and possibly nonzero monodromy. -/
abbrev LocalParameterObjects :=
  WeilDeligneRepresentation.ParameterObjects.{u, v}
    (ν := (localNormCharacter F).toMonoidHom) (localInertia F)

/-- Genuine local parameter isomorphism classes. -/
abbrev LocalParameterClasses :=
  WeilDeligneRepresentation.ParameterClasses.{u, v}
    (ν := (localNormCharacter F).toMonoidHom) (localInertia F)

/-- Genuine local parameter classes in every rank, including rank zero internally. -/
abbrev LocalParameterClassesOfRank (n : ℕ) :=
  WeilDeligneRepresentation.ParameterClassesOfRank.{u, v}
    (ν := (localNormCharacter F).toMonoidHom) (localInertia F) n

/-- Frobenius semisimplicity uses the actual geometric degree, not zero monodromy. -/
def IsLocalFrobeniusSemisimpleParameter
    (A : LocalWeilDeligneRepresentation.{u, v} F) : Prop :=
  WeilDeligneRepresentation.IsFrobeniusSemisimpleParameter (localInertia F)
    (localDegree F).toMonoidHom A

/-- The local Langlands parameter class set with unrestricted nilpotent monodromy. -/
abbrev LocalFrobeniusSemisimpleParameterClassesOfRank (n : ℕ) :=
  WeilDeligneRepresentation.FrobeniusSemisimpleParameterClassesOfRank.{u, v}
    (ν := (localNormCharacter F).toMonoidHom)
    (localInertia F) (localDegree F).toMonoidHom n

/-- The actual zero-monodromy functor at the constructed local field data. -/
def localZeroMonodromyFunctor :
    LocalWeilRepresentation.{u, v} F ⥤ LocalWeilDeligneRepresentation.{u, v} F :=
  WeilDeligneRepresentation.zeroMonodromyFunctor (localNormCharacter F).toMonoidHom

/-- Every intertwiner lifts uniquely under the local zero-monodromy functor. -/
def localZeroMonodromyFullyFaithful : (localZeroMonodromyFunctor.{u, v} F).FullyFaithful :=
  WeilDeligneRepresentation.zeroMonodromyFullyFaithful (localNormCharacter F).toMonoidHom

/-- Zero monodromy preserves the actual open-inertia parameter convention. -/
def localZeroMonodromyParameter (A : LocalOpenInertiaWeilObjects.{u, v} F) :
    LocalParameterObjects.{u, v} F :=
  WeilDeligneRepresentation.zeroMonodromyParameter (localInertia F)
    (localNormCharacter F).toMonoidHom A.val A.property

end Langlands.Weil.Local
