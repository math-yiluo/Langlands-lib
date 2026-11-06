# Pinnings on actual split reductive groups over fields

This module specializes Conrad, *Reductive group schemes* (2014),
Definition 6.1.1, printed/PDF p.186, to an arbitrary field `k : Type u`.
Conrad chooses a base of the root system and a trivializing section of
each simple-root Lie line. Over a field a trivialization is a linear
equivalence from `k` to that line. The associated root vector is the
image of `1`.

`RootPinning i P b` records these linear equivalences for the simple-root
indices in the support of the Mathlib base `b`. Their targets are the
published actual submodules `weightSpace i (P.root a)` of the dual-number
identity kernel of `G`. Weight membership therefore retains its tests
over every coefficient algebra. This standalone structure does not
assert that `P` is the root datum of `i`; that assertion is the separate
published predicate `IsRootDatumOf`.

The implemented elementary lemmas prove that each chosen vector belongs
to its specified actual weight space and is nonzero. The latter follows
from injectivity of the trivialization and `1 ≠ 0` in the field. Linearity
shows that evaluation at `c` is scalar multiplication of the root vector
by `c`. These consequences are internally derived from the definition.

`SplitPinning G` bundles actual connected reductivity, a split maximal
torus with its inclusion into `G`, a finite root index type, a reduced
Mathlib root datum satisfying `IsRootDatumOf`, a base, and its
`RootPinning`. The character and cocharacter lattices are those of this
actual torus. Over the field these actual character lattices provide the
lattice in Conrad's split triple; an additional abstract lattice label
is not introduced.

`SplitPinning.Iso p q` records an actual group-scheme isomorphism, an
actual torus isomorphism and their commuting inclusion square, a
bijective indexing of all roots and coroots agreeing with the induced
lattice maps, preservation of the simple-root supports, and equality of
the chosen root vectors under the actual linear differential. This is
the field isomorphism interpretation of pinning compatibility described
on Conrad p.187 and used in the discussion on p.243 preceding
Proposition 7.1.6. The differential and lattice maps are the published
actual transport constructions. No assertion about general isogenies
or Frobenius compatibility is made.

These are definitions of data and their elementary consequences.
Existence of such data, existence or uniqueness of pinned
isomorphisms, and the automorphism-group splitting are separate proof
obligations. This module supplies none of those assertions and does not
prove quasi-split inner-form existence.
