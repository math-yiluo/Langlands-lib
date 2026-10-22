# Finite-index induction on exact virtual representations

Worker 20 constructs induction on the exact-relation virtual representation
group and on its genuine degree-zero submodule. The underlying representation
is the existing equivariant-function induction from
`Langlands.Weil.Representation.Induction`; no new representation model or
irreducible decomposition is introduced.

## Exactness of the actual construction

Let `K` be a field, `G` a group and `S` a finite-index subgroup of `G`.
The coefficient, group and source-carrier universes are independent.
The source objects have carrier universe `uV`; the induced function spaces
have carrier universe `max uG uV`. The source and target predicates below
reflect this necessary universe change.

The published `Induction.coordinates S A` identifies the actual induced
space with functions from the right-coset quotient to the carrier of `A`.
`coordinates_induceMap` records that an induced intertwiner acts pointwise
in those coordinates.

`isShortExact_induce` proves that finite-index induction preserves all three
conditions in `FiniteRepresentation.IsShortExact`: injectivity, surjectivity,
and equality of range and kernel. Injectivity is checked in each coset
coordinate. For surjectivity, a preimage of each coordinate is chosen under
the original surjective map and then transported back by the coordinate
equivalence. The inclusion of the induced range in the induced kernel
follows coordinatewise from the original exactness. Conversely, each
coordinate of an element of the induced kernel lies in the original range;
choosing those preimages and applying the inverse coordinate equivalence
gives a preimage under the induced first map.

These choices are ordinary vector preimages. The construction neither
assumes nor selects an equivariant splitting of the original sequence.
The finite-dimensionality and rank of the induced representation are the
published results about this same equivariant-function model.

## Descent to virtual representations

`P` selects representations of `S`, and `Q` selects representations of `G`.
The caller supplies exactly the object-closure implication
`hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A)`.
This is not an assumption of exactness: exactness has already been proved
for all representations. It records that the chosen source and target
families contain the relevant objects. No closure, continuity or
semisimplicity theorem is silently attached to an arbitrary predicate.

`induceClassWith` descends actual induction to the existing isomorphism
classes, using the published induction of genuine intertwining
equivalences. `induceClassWith_isExactAdditive` combines the exactness proof
with the defining exact relation in the target virtual group. The
universal quotient lift from `Langlands.VirtualRepresentation.Exact`
therefore constructs `ExactGrothendieckGroup.induce` as an integer-linear
map. Its action on genuine classes and on actual representations is proved.

`degree_comp_induce` proves equality of linear maps

```
degree_Q ∘ induce = [G:S] • degree_P.
```

The proof uses the quotient's generator-extensionality theorem, reduces to
a genuine isomorphism class and then an actual representation, and applies
the published formula `FiniteRepresentation.rank_induce`. The pointwise
version is `degree_induce`. Consequently `induceDegreeZero` is the
restriction of the actual induction map to the kernel of degree.
Its subtype certificate follows from this proved formula. It applies to
all virtual degree-zero elements, including nonzero differences of
representations of equal rank.

`induceAll` specializes both object predicates to `True`. This gives an
unconditional algebraic induction map, with no extra closure hypothesis.

## Source correspondence and scope

John Tate, *Number theoretic background*, Corvallis Part II (1979),
section 2 opening and section 2.1, printed pages 9–10 / retained PDF pages
18–19, defines the exact-additive virtual representation group and the
restriction and induction maps for finite extensions of local or global
fields. The reason given for induction is the finite-index embedding of
the smaller Weil group. The original pages were read directly for this
construction.

- Literature ID: `tate-1979-number-theoretic-background`.
- Retained source:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
- SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*
(1973), Theorem 4.1(1)–(3), printed page 535 / internal and retained PDF page
35, extends epsilon constants by exact additivity to virtual representations
and requires induction compatibility on virtual representations of degree
zero. The original page was read and visually inspected, including the
trace composition in (3). This module constructs the virtual induction
map needed for that condition. It does not formulate or prove the
epsilon identity itself.

- Literature ID: `deligne-1973-local-constants`.
- Retained source:
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- SHA-256:
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

This is an explicitly derived algebraic generalization of the source's
continuous complex Weil representations. The proofs concern actual
finite-dimensional representations over any field and a finite-index
subgroup of any group. They are intrinsic construction obligations for
the quotient map, not claimed as separately numbered source theorems.
Topological continuity, the identification of actual local Weil groups
under field extensions, trace pullback of characters, reciprocity and
nonabelian epsilon-system existence remain separate obligations.

The imports `Langlands.VirtualRepresentation.Exact` and
`Langlands.Weil.Representation.Induction` are published Library modules.
