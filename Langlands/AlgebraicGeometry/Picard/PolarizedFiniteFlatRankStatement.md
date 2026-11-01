# Native rank of a polarized finite flat endomorphism

`Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankStatement` is an
unproved proposition target for general scheme geometry. Let `K` be an
algebraically closed field and let `X` be an actual scheme over `Spec K`,
smooth of specified relative dimension `g`, proper, and geometrically
connected. Let `f : X ⟶ X` be an endomorphism over `Spec K` whose underlying
scheme morphism is finite and flat. For an actual ample line bundle `L` on
`X` and a positive natural number `q`, assume an isomorphism of the actual
module sheaves

```text
f* L ≅ L^(tensor q).
```

The conclusion is `f.left.finrank x = q ^ g` at every target point `x`.
Here `finrank` is Mathlib's native `Scheme.Hom.finrank`, defined by the rank
of the actual finite algebra on affine charts. No number called a degree is
supplied as data.

The line bundle is the Library's locally free rank-one module sheaf.
`L.IsAmple` is its published affine section-locus criterion. Pullback is
`Scheme.Modules.pullback`, and the power is the actual
`Langlands.Scheme.Modules.tensorPow`. `SmoothOfRelativeDimension` is
Mathlib's standard-smooth-chart condition. The equation defining the
over-category morphism ensures that `f` is a morphism over the specified
field. The target permits `q = 1` and `g = 0`.

The statement is derived from the original Stacks Project material retained
as `stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`,
directory fingerprint
`e416e1999a1cefab5de7c4d444e6a8dfc0a3da10dc3c842df6c57cb15bce8a72`.
In `0BEL.html`, Section 33.45, Lemmas 33.45.5 and 33.45.9 give
multilinearity and positivity of ample intersection numbers. Definition
33.45.10 defines the ample degree. Lemma 33.45.11 (`0BEX.html`) compares
the degree of a pullback with the degree of a finite dominant map. These
imply that a polarized endomorphism of a proper integral variety of
dimension `g` has degree `q ^ g`: multiply its positive ample degree by
either the map degree or `q ^ g`, then cancel.

The formulation uses smooth geometrically connected schemes over an
algebraically closed field. Passing to the nonempty case gives an integral
variety of dimension `g`. A finite flat endomorphism has nonempty open and
closed image, hence is surjective. Its native rank is locally constant and
therefore constant; at the generic point it agrees with the function-field
degree of Stacks Definition 29.52.8 (`02NY.html`). Section 29.49
(`02K9.html`), Definition 29.49.1 and Lemmas 29.49.2 and 29.49.5, supplies
the finite locally free rank convention. These geometric and rank
identifications are part of the intended proof obligation, rather than
extra hypotheses or proved results of this file. If the scheme is empty,
the pointwise conclusion is vacuous. No matching project errata file was
present when this statement was prepared.

This file states a general prerequisite. It contains no abelian scheme or
torsion module and proves no numerical rank formula. Applying a future
proof to actual multiplication requires separate theorems supplying the
actual ample line bundle and pullback identity, and the existing comparison
from actual torsion cardinality to native multiplication rank.
