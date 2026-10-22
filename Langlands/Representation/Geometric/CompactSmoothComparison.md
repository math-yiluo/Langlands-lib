# Canonical compact-to-smooth induction and support quotients

Author: Worker 181.

This internal construction packages the published canonical inclusion
bijectivity into natural isomorphisms of the actual induction functors,
their actual support subfunctors, and their actual successive quotients.
The pair reuses the quotient-map construction from
[`Filtration/IsoTransport`](../Filtration/IsoTransport.md).

## Scope and conventions

The induction comparison uses a commutative ring `R : Type uR`, a group
`G : Type uG` with `TopologicalSpace G` and `IsTopologicalGroup G`, and an
arbitrary subgroup `P`. Its one extra hypothesis is
`CompactSpace (Induction.LeftQuotient P)`. The input category is
`Rep.{uV} R P`, including arbitrary algebraic covariance representations.
The three universes are independent; the induced carrier universe is
`max uG uV`. No admissibility, smoothness of the covariance representation,
finite length, finite dimension, closedness of P, or Hausdorff assumption is
added. The outputs are smooth because the existing induction functors
already select smooth right-translation vectors.

The quotient is the existing topological left quotient `P \ G`. Functions
have left covariance and the action is right translation. The existing
compact-support condition is compactness of the projected nonzero support.
The comparison uses
`Induction.compactInclusion_bijective_of_compactSpace` from
[`CompactQuotientProof`](../Induction/CompactQuotientProof.md), which already
proves bijectivity without admissibility. This module does not reprove that
topological result.

## The canonical natural comparison

`Induction.compactSmoothInclusion P` has component at A equal to
`compactInclusion P A.ρ`, bundled as a smooth-representation morphism. Its
naturality is definitional: both induction functors act on morphisms by
postcomposition. This natural transformation itself needs no compactness.

`Induction.compactSmoothIso P` uses `IntertwiningMap.ofBijective` on those
same components and `NatIso.ofComponents`. Its forward natural transformation
is exactly `compactSmoothInclusion`, as `compactSmoothIso_hom` and
`compactSmoothIso_hom_app` record. The inverse comes from the inverse linear
equivalence; `compactSmoothIso_inv_apply_val` proves that forgetting its
compact-support certificate returns precisely the input smooth function.
The categorical isomorphism carries both inverse identities and naturality.

`Geometric.rawRestrictedCompactSmoothIso P Q` forgets the output smoothness
certificate and restricts the action to any subgroup Q. It compares exactly
`rawRestrictedCompactInduction P Q` and `rawRestrictedSmoothInduction P Q`.
Its forward map is the underlying subtype inclusion, as the explicit
`rawRestrictedCompactSmoothIso_hom_apply` law states.

## Actual support subfunctors

For any right-Q-invariant subset U of `P \ G`,
`rawSupportCompactSmoothMap P Q U hU` sends a supported compact function f
to the same smooth function, carrying along the identical pointwise support
proof. The map is linear, Q-equivariant and natural by definitional equality.
No openness assumption on U is required.

Under compactness, `rawSupportCompactSmoothIso P Q U hU` makes this map a
natural isomorphism between the existing `rawSupportSubfunctor` and
`rawSmoothSupportSubfunctor`, each viewed through `toFunctor`. Injectivity
is subtype injectivity. Surjectivity follows by lifting a smooth function
through the published compact-inclusion bijectivity and transporting its
unchanged support proof. Its inverse again returns exactly the same underlying
smooth function, proved by `rawSupportCompactSmoothIso_inv_apply_val`.

The `_hom` and `_hom_apply_val` laws fix the forward map explicitly.
`rawSupportCompactSmoothIso_inclusion` is an equality of natural
transformations: comparison on support followed by inclusion equals inclusion
followed by the ambient restricted comparison. Thus the support isomorphism
is compatible with the given embeddings into induction.

## Quotient transport and the specified filtration

The imported generic helper `RepSubfunctor.quotientNatMap S T S' T' e h` descends
a natural map between upper subfunctors when it sends the pulled-back lower
submodules into each other. It uses the existing quotient objects and
`Submodule.mapQ`. Equivariance and naturality are proved on representatives
using surjectivity of the canonical quotient projections. Its projection law
is definitional.

`RepSubfunctor.quotientNatIso` takes an upper natural isomorphism and an
if-and-only-if membership condition on those lower submodules. The inverse
preserves the denominator by this equivalence and the original inverse
identity. Both descended inverse identities are proved on representatives.
The `_hom_projection` and `_inv_projection` laws identify both quotient maps
on classes. This helper only needs a monoid and commutative coefficients;
it is independent of topology and works for different ambient functors with
the same representation carrier universe. Without containment of S in T,
the existing quotient model is T/(S intersect T); with containment it is T/S.

For a fixed `s : OrderedDoubleCosets P Q n`,
`OrderedDoubleCosets.rawSupportStepCompactSmoothIso s k` compares step k
of `s.rawSupportFiltration` with step k of `s.rawSmoothSupportFiltration`.
Its inclusion law uses the same ambient comparison at every step.
`rawSupportGradedCompactSmoothIso s i` applies the generic quotient
isomorphism to steps `i.castSucc` and `i.succ`. Membership in the lower
support submodule is definitionally unchanged by the upper comparison.

These are actual natural isomorphisms of the already specified graded
functors. The same s and i occur on both sides; no filtration, representative,
or ordering is replaced. The `_hom_projection` formula sends the class of f
to the class of its unchanged smooth function. The `_projection` theorem
expresses this as a commuting diagram of natural transformations. Inverse
and naturality laws are supplied by the constructed natural isomorphism.

## Provenance and boundary

The definitions and transport arguments are internal consequences of the
imported function models, the published inclusion bijectivity, and the
existing filtration quotient construction. Their representation-theoretic
context is Bernstein and Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977): section 1.8, printed page 444 (PDF page 5), defines
the two induction functors; proposition 1.9(e), printed page 445 (PDF page 6),
states their coincidence for compact quotient; sections 5.3–5.4, printed
page 461 (PDF page 22), use invariant support subspaces and their successive
quotients. These three original pages were read for this contribution.

Registered source: `bernstein-zelevinsky-1977-induced-i`; PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The broader coefficient and topological scope follows from the imported
helper and the implemented algebraic constructions, not from a claim that
BZ's full geometric lemma holds in this generality.

Precomposing the resulting natural isomorphisms with a covariance functor
retains that functor, including any positive half-modulus twist it supplies.
No concrete p-adic specialization is defined here. Orbit restriction,
Jacquet comparison, and geometric-lemma orbit-piece identifications remain
outside this construction.

## Development checks

The complete module and a private consumer file pass the project's Lake build
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Unapplied signature
assignments check `compactSmoothIso` and `rawSupportGradedCompactSmoothIso`
with independent coefficient, group, and input carrier universes. Inspection
reports the latter's universe parameters as `uR`, `uG`, `uV`. The induction,
support, and graded isomorphisms depend only on `propext`, `Classical.choice`,
and `Quot.sound`. There are no errors or warnings. These development checks
are separate from independent review and publication.
