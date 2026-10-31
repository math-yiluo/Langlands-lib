# Canonical Grothendieck maps for the actual normalized parabolic functors

Author: Worker 23.

`Langlands.Parabolic.normalizedParabolicGrothendieck.{uF,uV} F T` proves
exactly
`Langlands.Parabolic.NormalizedParabolicGrothendieckStatement.{uF,uV} F T`
from
[`Parabolic.FiniteLengthGrothendieckStatement`](FiniteLengthGrothendieckStatement.md).
Its only outer parameters are `{p : ℕ} [Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, and arbitrary supplied `T : F.TopologicalData`.
There are no further hypotheses, and no data or instances carrying
finite-length preservation, exactness, admissibility or any other conclusion.

The theorem is the conjunction of the two clauses of the statement. For every
rank `n : ℕ` and block shape `B : GeneralLinear.BlockShape n`, the induction
clause gives a unique integer-linear map from
`B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier` to
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier`. It sends the
class of every finite-length smooth product-Levi representation `A` to the class
of `(T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A`. The
Jacquet clause gives the unique map in the reverse direction, sending the class
of every finite-length smooth GL representation to the class of its image under
`T.normalizedJacquetFunctor.{uF, max uF uV} B`. In both clauses the finite
length of the actual output is proved as part of the conclusion. The groups are
the exact finite-length Grothendieck groups, with relations from all actual
short exact sequences, including nonsplit ones.

## Implemented proof

All helpers are in the namespace
`Langlands.Parabolic.FiniteLengthGrothendieckAssembly`.

### Generic existence and uniqueness

`existsUnique_functorMap` is stated for an arbitrary functor
`Φ : SmoothRep R G ⥤ SmoothRep S H` between smooth representation categories at
arbitrary universes. It assumes the published predicates
`SmoothRep.PreservesFiniteLength Φ` and
`SmoothRep.PreservesFiniteLengthShortExact Φ`. It concludes the unique
existence of an integer-linear map `l` with

`∀ A hA, ∃ hOut : (Φ.obj A).HasFiniteLength,
  l (ofRepresentation A hA) = ofRepresentation (Φ.obj A) hOut`.

This is exactly the generator property of the target clauses.

- Existence. The witness is the published generic map
  `SmoothRep.FiniteLengthGrothendieckGroup.map Φ hl hx` from
  [`Smooth.FiniteLengthGrothendieckFunctor`](../Smooth/FiniteLengthGrothendieckFunctor.md).
  For each `A` and `hA`, the output-length witness is `hl A hA`. The generator
  equality is the published `map_ofRepresentation`.
- Uniqueness. Let `l` be any integer-linear map with the generator property.
  `SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object` from
  [`Smooth.FiniteLengthGrothendieck`](../Smooth/FiniteLengthGrothendieck.md)
  reduces `l = map Φ hl hx` to equality on every finite-length object `A`.
  The generator property of `l` supplies some witness `hOut` and the equation
  `l (ofRepresentation A hA) = ofRepresentation (Φ.obj A) hOut`. The generic
  map's equation has the output class with witness `hl A hA`. The two witnesses
  are proofs of the same proposition, so the classes agree by definitional
  proof irrelevance, and the two equations combine. Uniqueness therefore holds
  among all maps satisfying the entire existential property, as the statement
  requires. No family of witnesses is fixed in advance.

The groups and the generic map are reused. The proof does not rebuild them.

### Short-exact adapters

`SmoothRep.PreservesFiniteLengthShortExact Φ` asks that for every sequence
`f : A₁ ⟶ A₂`, `g : A₂ ⟶ A₃` of finite-length objects with
`IsShortExact (hom f) (hom g)`, the images satisfy
`IsShortExact (hom (Φ.map f)) (hom (Φ.map g))`. Here `IsShortExact` means
injectivity of the first intertwiner, surjectivity of the second, and equality
of range and kernel. The categorical smooth morphisms are read through their
underlying intertwiners `SmoothRep.hom`.

- `normalizedInductionFunctor_preservesShortExact` applies the published
  `Parabolic.normalizedInductionExactness F T B` from
  [`Parabolic.InductionExactnessProof`](InductionExactnessProof.md). It does so
  with the actual carriers, representations, intertwiners `hom f` and `hom g`,
  and the smoothness proofs of the three objects. The induced intertwiners of
  that theorem are the half-modulus twists of the inflated maps, followed by
  smooth induction. They are definitionally `hom` of the functor's morphisms,
  so its three conclusions give the three components of `IsShortExact` after
  reordering.
- `normalizedJacquetFunctor_preservesShortExact` applies the published
  `PadicField.TopologicalData.normalizedJacquetFunctor_map_exact` from
  [`Parabolic.NormalizedJacquetExactnessProof`](NormalizedJacquetExactnessProof.md).
  That theorem is already stated for the functor's morphisms. Its conclusion
  is reordered in the same way. The theorem is the functor form of the
  published `Parabolic.normalizedJacquetExactness` in the same module.

Both exactness inputs hold for all smooth short exact sequences. The
finite-length hypotheses of the predicate are therefore unused.

### The two clauses and the final theorem

`normalizedInductionGrothendieck` proves
`NormalizedInductionGrothendieckStatement.{uF, uV} F T`. It installs
`T.topology`, introduces `n` and `B`, and applies `existsUnique_functorMap` to
`T.normalizedParabolicInductionFunctor.{uF, max uF uV} B`. Finite-length
preservation is the induction conjunct of the published
`Langlands.Parabolic.normalizedParabolicFiniteLength.{uF, max uF uV} F T`
from [`Parabolic.FiniteLengthFunctorProof`](FiniteLengthFunctorProof.md),
specialized to `n` and `B`. Short-exact preservation is the induction adapter.

`normalizedJacquetGrothendieck` is the same argument for
`T.normalizedJacquetFunctor.{uF, max uF uV} B`, using the Jacquet conjunct of
the finite-length theorem and the Jacquet adapter.

The generic class map `SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation`
is definitionally the statement's `GeneralLinear.finiteLengthClass` and
`B.finiteLengthClass`. Likewise the generic groups are definitionally the
statement's specialized groups. The generic conclusion is therefore the target
clause without rewriting. `normalizedParabolicGrothendieck` pairs the two
clauses.

## Topology and normalization

The supplied `T` is arbitrary; it is not replaced by the canonical topological
data of `F`. Each clause installs only `T.topology`, as the statement does. The
induced topologies on `GeneralLinear n F.Carrier` and `B.Levi F.Carrier` are
those used by the published functors, the exactness theorems and the
finite-length theorem; the proof elaborates without any topology conversion.

The functors are the existing published ones, applied directly. Induction uses
the standard upper block parabolic, covariance by the positive half of the
block modulus `T.leviModulus B`, and right translation on smooth covariant
functions. Jacquet uses the actual coinvariants of the upper block unipotent
radical, with the Levi action twisted by the inverse half-modulus. No
replacement functor, opposite parabolic, contragredient, or change of
normalization occurs.

## Ranks, shapes and objects

Both clauses quantify every `n : ℕ` and every block shape internally, so rank
zero and its empty block shape are included. The finite-length theorem covers
all ranks and shapes, and the exactness theorems and generic argument need no
case split. Every smooth finite-length object of the actual categories is
covered. This includes zero representations and arbitrary smooth product-Levi
representations, with no tensor factorization. No admissibility,
irreducibility, central character or finite-dimensionality assumption is
added. Finite length means `IsFiniteLength` over the complex group algebra, not
finite complex dimension.

## Universes

The field level `uF` and carrier parameter `uV` are independent. All carriers
are in `Type (max uF uV)`. Both functors are applied at `.{uF, max uF uV}`, and
the finite-length theorem is applied at carrier level `max uF uV`. The
induction output category has carrier level `max uF (max uF uV)`. Lean
normalizes this to `max uF uV`, so the output is an object of the category of
the target Grothendieck group. The Jacquet functor retains the input level. No
resizing or comparison between different carrier levels is used. The closing
theorem's universe parameters are `uF` and `uV`, in that order.

## Imports and independence audit

The direct imports are the unchanged statement module
`Parabolic.FiniteLengthGrothendieckStatement`,
`Parabolic.FiniteLengthFunctorProof`, `Parabolic.InductionExactnessProof` and
`Parabolic.NormalizedJacquetExactnessProof`, all under
`Langlands.Representation`. The generic map module
`Smooth.FiniteLengthGrothendieckFunctor` is reached transitively.

The transitive project import closure of this module was computed from the
actual import lines at Library commit
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f`. Besides this module it has 598
project modules. All have nonempty paired Markdown. Each imported Lean and
Markdown file is byte-identical to that Library commit, so the statement pair
and everything it imports are unchanged.

The closure includes the finite-length theorem and its published inputs:
admissibility of smooth finite-length representations, finite length of
normalized product induction and irreducible-product induction, and the
Jacquet finite-length and finite-generation results. The task asks to
preserve Worker 395's finite-length task `2a216dfa`, Worker 325's tasks
`62571b78` and `0717fd42`, and Worker 122's task `dac75ee7`. This module uses
their work only through Worker 395's published theorem and its imports; it
duplicates none of their proofs. The closure also contains the definitional vocabulary
module `Classification.Segments`, which defines segments and multisegments and
records special constituents only by a relation. It contains no segment or
multisegment classification, exhaustion, existence or uniqueness statement.

Every closure Lean source, including this module, was scanned without case
sensitivity for the names of the excluded results and their proof modules.
These are analytic segment classification (`aca8805b`), special-head
multisegment exhaustion (`3bfb61fa`), ordered strong-head existence
(`ebea9a8a`), quotient coverage (`20e4e1c6`), tempered block uniqueness
(`52e97845`), `SquareIntegrableLanglandsClassification` (`1cb45da2`),
square-integrable exhaustion (`cd8ab97c`) and regular exhaustion (`bf433f0a`).
The scan covered the `SegmentEssentialSquareIntegrable`,
`MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
`QuotientExhaustion`, `TemperedBlockUniqueness`,
`SquareIntegrableLanglands{Classification,Exhaustion}` and
`RegularLanglandsExhaustion` stems, and there are no matches. None of these
conclusions, their proof successors, or their proof dependencies is an input.
No irreducible basis, alternating operator, involutivity or Aubert
irreducibility is proved or used.

## Provenance

This is an internal assembly. Its mathematical content is the universal
property of the exact Grothendieck group: an exact functor preserving finite
length induces a unique additive map on classes. The construction and its
uniqueness principle are the published generic units named above. The proof
supplies the actual preservation inputs and reconciles output-length witnesses.
The precise all-rank formulation, existential witnesses and universe choices
belong to the derived statement and are not attributed verbatim to literature.
The literature sources for normalization, exactness and finite length are
documented in the paired Markdown of the imported statement and proof modules.
