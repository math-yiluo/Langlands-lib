import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Predicates

/-!
# Complex Weil–Deligne parameter conditions and classes

The algebraic open-inertia convention and usual-topology continuity remain
separate. Frobenius semisimplicity is a condition on the Weil action.
-/

noncomputable section

universe uG uV

namespace Langlands.WeilDeligneRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] {ν : G →* ℂˣ}

/-- Tate's algebraic Weil–Deligne parameter condition on the underlying action. -/
def IsParameter (I : Subgroup G) (A : WeilDeligneRepresentation ℂ G ν) : Prop :=
  A.toFiniteRepresentation.HasOpenInertiaKernel I

/-- Usual-topology continuity of the underlying complex representation. -/
def IsContinuous (A : WeilDeligneRepresentation ℂ G ν) : Prop :=
  A.toFiniteRepresentation.IsContinuous

/-- Actual complex parameter objects with open inertia kernel. -/
def ParameterObjects (I : Subgroup G) :=
  {A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν // IsParameter I A}

/-- Pair isomorphism restricted to the specified open-inertia parameter condition. -/
def parameterSetoid (I : Subgroup G) : Setoid (ParameterObjects (ν := ν) I) :=
  Setoid.comap Subtype.val isomorphismSetoid

/-- Genuine classes of open-inertia-kernel Weil–Deligne parameters. -/
def ParameterClasses (I : Subgroup G) := Quotient (parameterSetoid.{uG, uV} (ν := ν) I)

/-- Forget the inertia condition on a class of pairs. -/
def parameterClassForget (I : Subgroup G) :
    ParameterClasses.{uG, uV} (ν := ν) I → IsomorphismClasses.{0, uG, uV} ℂ G ν :=
  Quotient.map Subtype.val (fun _ _ h => h)

/-- Rank-`n` genuine parameter classes, without Frobenius semisimplicity imposed. -/
def ParameterClassesOfRank (I : Subgroup G) (n : ℕ) :=
  {c : ParameterClasses.{uG, uV} (ν := ν) I // classRank (parameterClassForget I c) = n}

/-- Open inertia kernel and Frobenius semisimplicity are explicit, separate conditions. -/
def IsFrobeniusSemisimpleParameter (I : Subgroup G) (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation ℂ G ν) : Prop :=
  IsParameter I A ∧ A.IsFrobeniusSemisimple degree

/-- Pair isomorphism restricted to Frobenius-semisimple parameter objects. -/
def frobeniusSemisimpleParameterSetoid (I : Subgroup G)
    (degree : G →* Multiplicative ℤ) :
    Setoid {A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν //
      IsFrobeniusSemisimpleParameter I degree A} :=
  Setoid.comap Subtype.val isomorphismSetoid

/-- Genuine classes of Frobenius-semisimple parameters, with arbitrary nilpotent monodromy. -/
def FrobeniusSemisimpleParameterClasses (I : Subgroup G) (degree : G →* Multiplicative ℤ) :=
  Quotient (frobeniusSemisimpleParameterSetoid.{uG, uV} (ν := ν) I degree)

/-- Forget the conditions on a Frobenius-semisimple parameter class. -/
def frobeniusSemisimpleClassForget (I : Subgroup G) (degree : G →* Multiplicative ℤ) :
    FrobeniusSemisimpleParameterClasses.{uG, uV} (ν := ν) I degree →
      IsomorphismClasses.{0, uG, uV} ℂ G ν :=
  Quotient.map Subtype.val (fun _ _ h => h)

/-- The rank-indexed Frobenius-semisimple Weil–Deligne parameter set.
In particular, the definition does not require zero monodromy. -/
def FrobeniusSemisimpleParameterClassesOfRank (I : Subgroup G)
    (degree : G →* Multiplicative ℤ) (n : ℕ) :=
  {c : FrobeniusSemisimpleParameterClasses.{uG, uV} (ν := ν) I degree //
    classRank (frobeniusSemisimpleClassForget I degree c) = n}

/-- Embed an open-inertia-kernel Weil representation as an actual parameter with zero monodromy. -/
def zeroMonodromyParameter (I : Subgroup G) (ν : G →* ℂˣ)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.HasOpenInertiaKernel I) :
    ParameterObjects.{uG, uV} (ν := ν) I :=
  ⟨zeroMonodromy ν A, hA⟩

end Langlands.WeilDeligneRepresentation
