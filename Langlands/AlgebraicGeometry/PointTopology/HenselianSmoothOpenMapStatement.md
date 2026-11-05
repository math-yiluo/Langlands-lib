# Smooth rational-point openness over Henselian ultrametric fields

Author: Worker 1644. Target design and consumer motivation: Worker 1637.

`Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothRationalPointOpenMapStatement.{u}`
is a Prop-valued statement, with arbitrary universe `u`. It quantifies over:

- `K : Type u` with `NontriviallyNormedField K` and `IsUltrametricDist K`;
- `HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring`;
- actual objects `X Y : Over (Spec (CommRingCat.of K))`, with affine underlying schemes;
- an actual morphism `f : X ⟶ Y` with Mathlib's `AlgebraicGeometry.Smooth f.left`.

It asserts that postcomposition
`fun p : RationalPoint K X => p ≫ f` is an open map. Both point spaces are
equipped explicitly with the published `rationalPointTopology`. The carrier
`RationalPoint K X` is the actual morphism type
`Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X`. Its topology transports the
global-section evaluation topology along `rationalPointEquiv`. The statement
does not replace any point carrier, morphism, smoothness predicate or topology.

## Hypotheses and scope

`NormedField.valuation` sends `x` to `‖x‖₊`. Its valuation subring is therefore
the ring of elements of norm at most one. The Henselian hypothesis applies to
this ring, rather than to `K` as a local ring: every field is a Henselian
local ring in the latter, irrelevant sense. The topology on `K` is the one
provided by its given norm.

There is no completeness, local compactness, discrete-valuation, residue-field
perfection or characteristic restriction. In particular the statement allows
noncomplete Henselian fields in equal and mixed characteristic. Neither scheme
is required to be of finite type over `K`; smoothness imposes local finite
presentation on `f` itself. The conclusion also applies when the rational-point
spaces are empty, and asserts openness without asserting surjectivity.

## Provenance and intended mathematical route

This is derived internal analytic infrastructure, motivated by Kaletha and
Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12,
printed pp. 89–90 (PDF pp. 120–121). Their proof deduces openness on
`K`-points from smoothness of the algebraic torus norm. The authors'
*Corrections and additions* (1 November 2024), PDF pp. 24–25,
impose Henselian hypotheses in the surrounding valued-field setup.
The registered sources are `kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`)
and `kaletha-prasad-2024-corrections`
(SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`).
The generic affine statement here is our prerequisite formulation, rather
than a claim that those pages state it in this exact generality.

The intended proof first obtains local simple-root lifting over the Henselian
norm valuation ring. Translation and scaling put a polynomial near a chosen
simple root into an integral form with unit derivative. Hensel lifting then
gives nearby roots for sufficiently close coefficients, with control of their
distance from the original root. Applied to local standard-étale presentations,
this gives local lifting on point spaces; the nonvanishing localization
condition persists on a neighborhood. Smooth morphisms locally factor through
such étale maps and finite affine-space projections, whose maps on points are
open. Principal-open point charts and the actual coordinate homeomorphisms
transfer openness to the stated rational-point map.

For a base algebra of arbitrary size, each local presentation and each basic
evaluation neighborhood involves finitely many coefficients or functions.
This is the reason the route does not require finite type over `K`.
The existing `StandardEtalePoints` provides the actual point-coordinate
comparison without completeness. `StandardEtaleOpenProof` and
`SubmersiveOpenMap` use complete-field analytic inputs, and
`smoothRationalPointOpenMap` in `SmoothOpenMapProof` proves the local-field
statement. Those proofs do not supply the Henselian lifting step here.

This unit only defines the statement. Its proof, including the Henselian
lifting and local-to-global reductions, remains a separate obligation.
