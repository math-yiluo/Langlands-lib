# Finite-set affine neighborhoods of a finite-map scheme pushout

This file states
`Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutStatement.{u}`.
It contains no proof.

For arbitrary actual schemes `X`, `Y`, `Z`, `P` in the common universe
`u`, take actual morphisms
`i : Z ⟶ X`, `j : Z ⟶ Y`, `a : X ⟶ P`, and `b : Y ⟶ P`.
If `i` is a closed immersion, `j` is finite, every finite set of points
of `X` and of `Y` has an affine open neighborhood, and
`IsPushout i j a b`, then every finite set of points of `P` has an
affine open neighborhood.

The statement reuses
`Langlands.AlgebraicGeometry.PointTopology.HasFiniteAffineNeighborhoods`
from `PointTopology/AffineChartWeilRestrictionRepresentability.lean`.
That predicate is

```lean
∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.val
```

It concerns arbitrary finite sets of scheme points, including nonclosed
points. An affine open is an actual affine open subscheme of the scheme
in question. The pushout predicate is Mathlib's categorical universal
property in `Scheme`, with arbitrary schemes as target objects.
Its commutative square has top `i`, left `j`, right `a`, and bottom `b`.

## Original source and derived provenance

The original is Daniel Ferrand, *Conducteur, descente et pincement*,
Bulletin de la Société Mathématique de France 131 (2003), no. 4,
pp. 553–585, DOI
[10.24033/bsmf.2455](https://www.numdam.org/articles/10.24033/bsmf.2455/).
The registered source is
`ferrand-conducteur-descente-pincement-2003`, PDF SHA-256
`4f1f2438ad6d757d67d2ecf154b1bc920d210d8abd54c02e6acd020805629d91`.
The retained original is
`literature/Daniel Ferrand - Conducteur, descente et pincement (BSMF 131 no.4, 2003).pdf`.

Theorem 5.4(a), printed p. 570 (PDF p. 18), starts with a closed
subscheme `Y′` of `X′` and a finite map `g : Y′ → Y`. It defines
property (AF) by the existence of a single affine open containing each
finite set of points. Assuming (AF) for `X′` and `Y`, part (a)
asserts that their amalgamated ringed space is a scheme with (AF).
The proof of part (a) occupies printed pp. 570–572 (PDF pp. 18–20).
Section 4.2 and Scolie 4.3, printed pp. 566–567 (PDF pp. 14–15),
specify the ringed-space pushout and its underlying surjective map
from the disjoint union.

The correspondence is:

| Ferrand | Lean |
| --- | --- |
| `X′` | `X` |
| `Y′` | `Z` |
| `Y′ ↪ X′` | `i` |
| `g : Y′ → Y` | `j` |
| amalgamated scheme `X` | a scheme pushout of the span |
| `f : X′ → X`, `u : Y → X` | its two cocone maps |
| property (AF) | `PointTopology.HasFiniteAffineNeighborhoods` |

This is a derived consequence rather than a literal transcription.
First apply the source to the closed immersion `i`, using the
isomorphism between its domain and the corresponding closed subscheme.
The source constructs an AF scheme `Q` as a ringed-space pushout.
This is also a scheme pushout. Indeed, its two cocone maps are
scheme morphisms, and their images cover `Q`. The ringed-space
mediator to any scheme is local on stalks: at each point of `Q`,
use a point above it in one of the two source schemes. If an element
of the target stalk maps to a unit in the stalk of `Q`, it maps to
a unit in the stalk upstairs. The composite on stalks is local
because it is induced by a scheme morphism, so that element was
already a unit in the target stalk. Thus the mediator is local on
stalks and hence is a scheme morphism. Uniqueness is inherited
from the ringed-space universal property.

The two scheme pushout universal properties give the unique
isomorphism `e : Q ≅ P` compatible with the cocones. For a finite
set `s` of points of `P`, its image under `e.inv` is a finite set
of points of `Q`, so it lies in an affine open `V` of `Q`. The
isomorphism sends `V` to an affine open of `P` containing `s`.
This uses the underlying homeomorphism to transport open sets and
the induced isomorphism of open subschemes to preserve affineness.
Thus (AF) passes to `P`.
The future proof must implement both this construction or an equivalent
scheme argument and the transport. They are not supplied by the
present proposition definition.

For the source's local AF argument, a finite point set in the pushout
splits into a finite subset of `Y` and a finite subset of
`X′ \ Y′`. Finiteness of `g` makes the inverse image of the former
finite. The avoidance lemma 5.5 and the closedness of `g` produce
compatible affine opens in `X′` and `Y`; the affine pinching
construction then gives an affine neighborhood of the original
finite set. This describes the source route, not an implemented
Lean proof.

## Scope

There is no noetherian, reduced, separated, projective, flat,
quasi-compact, or surjectivity assumption. In particular, `j` need not
be surjective, and no finite-set restriction to closed points is made.
The finite-map hypothesis is retained; it is not replaced by
integrality alone.

The conclusion is only the finite-set affine-neighborhood property
of the supplied scheme pushout. The file proves no pushout existence,
pullback property, conductor construction, algebraic-space
identification, Picard comparison, universal-family classification,
or abelian-scheme representability.
