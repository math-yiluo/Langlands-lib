# Finite length from irreducible inputs

Authors: Worker 717, with Worker 117 (who proposed the signature), for task
174d2de0-fa21-41b4-b091-f1b86481790b. This module declares one proposition
definition and no theorem. It does not prove the proposition. The proof is
a separate unit, in the planned module
`Langlands.Representation.Smooth.FiniteLengthInduction`.

## The declaration

`Langlands.SmoothRep.FiniteLengthInductionStatement.{uR, uG, uV, uS, uH, uW}`
says: for every field `k : Type uR`, every group `G : Type uG` with a
topology, every commutative ring `S : Type uS`, every group `H : Type uH`
with a topology, and every functor

`Φ : SmoothRep.{uR, uG, uV} k G ⥤ SmoothRep.{uS, uH, uW} S H`,

if

1. `PreservesFiniteLengthShortExact Φ`, and
2. `(Φ.obj A).HasFiniteLength` for every `A` with `A.IsIrreducible`,

then `PreservesFiniteLength Φ`.

The word *induction* in the name means induction on the length. It does not
mean parabolic induction. `Φ` is an arbitrary functor.

## The predicates

All of these are existing Library definitions, reused by name.

- `SmoothRep.HasFiniteLength A` (`Category/Basic`) is Mathlib's
  `IsFiniteLength` for `A.representation.asModule` over the group algebra
  `R[G]`. It means finite composition length over the group algebra, not
  finite dimension. The zero representation has finite length.
- `SmoothRep.IsIrreducible A` (`Category/Basic`) is an abbreviation for
  Mathlib's `Representation.IsIrreducible A.representation`: the lattice of
  invariant submodules is a simple order. So an irreducible representation
  is nonzero. No finite dimension and no admissibility is required. This
  predicate needs a field of coefficients. That is why the source category
  is over a field `k`, while the target ring `S` is only a commutative ring.
- `SmoothRep.PreservesFiniteLength Φ` (`Smooth/FiniteLengthGrothendieckFunctor`)
  says that `(Φ.obj A).HasFiniteLength` holds whenever `A.HasFiniteLength` holds.
- `SmoothRep.PreservesFiniteLengthShortExact Φ` (same module) says: for
  morphisms `f : A ⟶ B` and `g : B ⟶ C` between three finite-length
  objects, if `IsShortExact (hom f) (hom g)` holds, then
  `IsShortExact (hom (Φ.map f)) (hom (Φ.map g))` holds. Here
  `SmoothRep.IsShortExact` (`Smooth/FiniteLengthGrothendieck`) means that
  the first underlying intertwiner is injective, the second is surjective,
  and the range of the first equals the kernel of the second. Exactness is
  assumed only on sequences of finite-length objects. Nothing is assumed
  about the images.

## Scope

- The groups `G` and `H` carry only a `Group` and a `TopologicalSpace`
  instance. No topological-group structure, local compactness or
  nonarchimedean property is assumed.
- The source coefficients form a field. The target coefficients form a
  commutative ring.
- The six universes are independent.
- Hypothesis 2 concerns all irreducible smooth representations, admissible
  or not. The conclusion gives only finite length of the images. It gives
  no bound on the length.

## Why the assertion holds (not proved here)

The expected proof is induction on the length of `A`.

- *Length zero.* The carrier of `A` is trivial. The pair `(𝟙 A, 𝟙 A)` is
  short exact, because on a trivial module the range and the kernel of the
  identity are both the whole module. Hypothesis 1 makes
  `(Φ.map (𝟙 A), Φ.map (𝟙 A)) = (𝟙 (Φ.obj A), 𝟙 (Φ.obj A))` short exact.
  The range of the identity is then the zero kernel, so `Φ.obj A` is trivial
  and has finite length.
- *Positive length.* `A` has a simple invariant submodule `A'`. It is a
  smooth irreducible subrepresentation in the same carrier universe. The
  quotient `A / A'` is smooth and has smaller length. The inclusion and the
  projection form a short exact sequence of finite-length objects.
  Hypothesis 1 makes its image short exact. Hypothesis 2 gives finite length
  of `Φ.obj A'`, and the induction hypothesis gives finite length of
  `Φ.obj (A / A')`. An extension of two finite-length modules has finite
  length, so `Φ.obj A` has finite length.

## Provenance

This statement is derived, not quoted. Renard (2026), Chapter VI, §VI.6.2
"Induction et longueur finie", printed page 178 (PDF page 184), announces
that the induction functor `i_P^G` preserves modules of finite length. The
Lemma there proves only the case of an irreducible representation `(τ, E)`
of `M`, using the exactness of `i_P^G`. The passage from irreducible inputs
to all finite-length inputs is left implicit. The same dévissage appears
explicitly in the proof of the converse direction of the Theorem in §VI.6.3,
printed page 179 (PDF page 185): "un raisonnement par récurrence sur la
longueur", which uses the exactness of `V ↦ V^K` for lengths `n ≥ 2`. This
module states that step for an arbitrary functor between actual smooth
representation categories. It assumes only exactness on finite-length short
exact sequences, which is what the induction on length uses.

## Relation to the task

The exact target of task 174d2de0 is
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement`
(`Aubert/General/PrerequisiteStatements`). It is `PreservesFiniteLength` of
the actual dynamic normalized induction functor
`normalizedInductionFunctor (dynamic_isSemidirectDecomposition χ _) hU`.
This proposition splits that target into two inputs: exactness of this
functor on finite-length sequences, and finite length of its value on
irreducible representations of `Z(χ)(F)` (the Lemma of Renard VI.6.2). This
module states neither input for the dynamic functor.
