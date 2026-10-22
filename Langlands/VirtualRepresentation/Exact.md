# Exact-sequence virtual representations

Worker 20 constructs `Langlands.VirtualRepresentation.ExactGrothendieckGroup P`
from actual finite-dimensional representations over a field. This is the exact
relation quotient needed before formulating nonabelian local constants on
virtual representations. It is not a free group on irreducible classes, and no
irreducible decomposition or semisimplicity theorem is assumed.

## Objects, relations and universes

The coefficient field, acting monoid and vector-space carrier have independent
universes. The type `FiniteRepresentation K G` is the published full subcategory
of Mathlib representations with finite-dimensional actual carriers. A predicate
`P` selects the objects under consideration. The published
`IsomorphismClassesWith P` identifies two such objects exactly when there exists
an invertible linear intertwiner between their actual representations.

`ExactPresentation P` is the existing `IntegralLattice` on these genuine classes.
Thus its elements are finitely supported integral combinations of isomorphism
classes, not formal names supplied independently of representations.

`FiniteRepresentation.IsShortExact f g` asserts injectivity of the first actual
intertwiner, surjectivity of the second, and equality of the first map's range
with the second map's kernel. These are precisely the endpoint and middle
conditions for an exact sequence

```
0 -> A --f--> B --g--> C -> 0.
```

For every such sequence whose three objects satisfy `P`, `exactRelationSet P`
contains `[B] - [A] - [C]`. `exactRelations P` is their integral span, and
`ExactGrothendieckGroup P` is the actual quotient module by this span. It has the
resulting additive commutative group and integer-module structures. The
construction does not replace exact sequences by split exact sequences.

A general predicate need not define an extension-closed exact category. In that
generality the name denotes precisely the displayed quotient by those actual
short exact sequences with all three terms in the selected family. No closure
axiom or exact-category theorem is included as an assumed field. For the intended
continuous-representation specialization, the ordinary continuous predicate is
to be supplied from the existing parameter definitions, with its own closure
facts kept separate. The topology is not silently replaced by the discrete one.

## Class map and universal property

`quotientMap`, `ofClass` and `ofRepresentation` are concrete maps into this
quotient. An actual representation equivalence gives equality of virtual
classes. `ofRepresentation_shortExact` proves `[B] = [A] + [C]` by showing the
corresponding relation lies in the defining submodule.

For a function `a` on genuine classes with values in an abelian group, viewed
as its canonical integer module, `IsExactAdditive P a` says exactly that
`a(B) = a(A) + a(C)` for every actual short exact sequence in the family.
`relations_le_ker_extend` proves that the integral linear extension kills every
generating relation, hence their span. `lift` is the quotient linear map this
proof permits. Its values on actual classes and representations are proved.

`hom_ext` proves that maps out of the quotient are determined by their values
on genuine classes, using the single-coordinate generators of the integral
presentation and surjectivity of the quotient map. `existsUnique_lift_iff`
proves the full equivalence between exact additivity and existence of a unique
extension. In the reverse direction, the extension must respect the already
proved relation. This is an actual universal property of the constructed group,
not an assumption that an epsilon function satisfying additional properties
exists. Multiplicative abelian targets, such as complex units, can be used by
applying this interface to their additive type synonym.

## Degree

`rank_eq_add_of_shortExact` proves rank additivity over any field, with three
independent carrier universes. Rank-nullity for `g` identifies the middle rank
with the ranks of its range and kernel. Surjectivity identifies its range with
the whole last space; exactness identifies its kernel with the first map's
range; injectivity identifies that range's rank with the first space's rank.
No equivariant splitting is selected.

`classDegree` sends a genuine class to its nonnegative rank, cast to the
integers. The proved rank formula shows that it is exact-additive, so `degree`
is its actual descended integer-valued linear map. `degree_ofRepresentation`
identifies its value with the original rank. `degreeZero` is its genuine kernel,
including virtual differences of equal rank. Negative and zero virtual degrees
are allowed; no positivity is imposed on virtual elements.

## Source and dependency correspondence

The original source is John Tate, *Number theoretic background*, Corvallis
Part II (1979), section 2 opening, printed page 9 / PDF page 18. Tate defines
the genuine isomorphism classes `M(G)`, virtual representations `R(G)`, and the
criterion that a class function to an abelian group extend uniquely when it
respects actual exact sequences. The retained original page was read directly
for this construction. The source uses multiplicative notation for the target
abelian group; the Lean construction uses additive notation without changing
the criterion. The extension to arbitrary fields and monoids is an explicitly
derived algebraic generalization of the same presentation. The rank argument
is the standard rank-nullity proof, not a claim that Tate states a separately
numbered dimension theorem on that page.

- Literature ID: `tate-1979-number-theoretic-background`.
- Original: `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
- Retained original SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `Langlands.Weil.Representation.Basic` supplies the actual finite representation
  objects, intertwining equivalences, isomorphism quotients and class ranks.
- `Langlands.VirtualRepresentation.Integral` supplies the existing finitely
  supported integer module, its generator and linear extension. This import
  preserves Worker 24's independent construction and does not reinterpret it
  as an exact-relation group.
- Pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0,
  supplies submodule spans and quotients, integral-module maps, and rank-nullity.

The project imports are published in Library
`459d17160ca3aef5c5b4e8ba056125e56d9479a0`. No pending Weil-Deligne kernel module
or actual local-field Weil assembly is imported. Identification with a split
Grothendieck group or an irreducible basis, induction on exact virtual groups,
local-field extension and reciprocity compatibility, and nonabelian epsilon
existence/uniqueness remain distinct obligations. This pair does not prove or
assume those results.
