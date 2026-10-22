import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Basic.Complex.Basic

/-!
# Relations describing actual irreducible constituents

These relations do not choose a special or Langlands quotient. In particular,
`IsIrreducibleHead` requires uniqueness of the kernel of an irreducible quotient,
not merely uniqueness of the isomorphism class of its target.

The common carrier universe is explicit. No finite-dimensionality assumption
is imposed. These algebraic relations can be applied to smooth representations.
-/

namespace Langlands.Classification

universe uG uV uC

variable {G : Type uG} [Group G]
variable {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- An irreducible quotient is witnessed by an actual surjective intertwiner. -/
def IsIrreducibleQuotient (ρ : Representation ℂ G V)
    (π : Representation ℂ G W) : Prop :=
  Representation.IsIrreducible π ∧
    ∃ q : ρ.IntertwiningMap π, Function.Surjective q

/-- An irreducible subrepresentation is witnessed by an actual injective
intertwiner. -/
def IsIrreducibleSubrepresentation (ρ : Representation ℂ G V)
    (π : Representation ℂ G W) : Prop :=
  Representation.IsIrreducible π ∧
    ∃ j : π.IntertwiningMap ρ, Function.Injective j

/-- The irreducible head relation includes uniqueness as a quotient object:
all irreducible quotient maps have the same kernel subspace of the source.
It asserts neither existence for every `ρ` nor a choice of quotient. -/
def IsIrreducibleHead (ρ : Representation ℂ G V)
    (π : Representation ℂ G W) : Prop :=
  Representation.IsIrreducible π ∧
    ∃ q : ρ.IntertwiningMap π, Function.Surjective q ∧
      ∀ (W' : Type uV) [AddCommGroup W'] [Module ℂ W']
        (π' : Representation ℂ G W'), Representation.IsIrreducible π' →
        ∀ q' : ρ.IntertwiningMap π', Function.Surjective q' →
          q'.toLinearMap.ker = q.toLinearMap.ker

/-- The irreducible socle relation includes uniqueness as a subobject:
all irreducible embeddings have the same image subspace of the ambient
representation. It makes no choice of an irreducible subrepresentation. -/
def IsIrreducibleSocle (ρ : Representation ℂ G V)
    (π : Representation ℂ G W) : Prop :=
  Representation.IsIrreducible π ∧
    ∃ j : π.IntertwiningMap ρ, Function.Injective j ∧
      ∀ (W' : Type uV) [AddCommGroup W'] [Module ℂ W']
        (π' : Representation ℂ G W'), Representation.IsIrreducible π' →
        ∀ j' : π'.IntertwiningMap ρ, Function.Injective j' →
          j'.toLinearMap.range = j.toLinearMap.range

/-- Scalar action of a prescribed character along an actual homomorphism.
For central characters one specializes `z` to the central inclusion or the
scalar-matrix inclusion. The relation does not assert character existence. -/
def HasScalarCharacter {C : Type uC} [Group C]
    (ρ : Representation ℂ G V) (z : C →* G) (ω : C →* ℂˣ) : Prop :=
  ∀ (c : C) (v : V), ρ (z c) v = (ω c : ℂ) • v

end Langlands.Classification
