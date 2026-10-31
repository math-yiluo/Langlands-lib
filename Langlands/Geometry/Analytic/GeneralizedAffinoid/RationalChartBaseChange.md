# Coefficient pullback of actual positive-radius rational charts

Author: Worker 56.

This module constructs coefficient pullback of the existing chosen rational
charts and their actual bounded restrictions. It is an internal derivation from
the published scalar rational quotient transport and bounded pushout. No
universal-property witness or arrow inferred only from locus containment is
supplied as input.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.
Fix an ultrametric normed field `K`, presented affinoid algebras `A,B`, and an
arbitrary bounded `K`-algebra homomorphism `φ : A → B`.

The noncomputable `coefficientRepresentative B b` chooses a scalar weighted
series mapping to `b : B` under the actual presentation map; its existence is
the published `presentationMap_surjective`. The theorem
`presentationMap_coefficientRepresentative` proves that its image is `b`.
For a chosen chart `d` over `A`, `pullback φ d` keeps its finite arity and
positive radii. Its denominator and numerators are these chosen representatives
of `φ(q_A(d.denominator))` and `φ(q_A(d.numerators j))`. Unit generation in `B`
is proved by `BaseChange.generatesUnitIdeal` from the generation in `d`, rather
than supplied separately. The class formulas, arity and radius formulas are
proved explicitly.

`pullback_locus` gives exact equality of subsets

```text
(pullback φ d).locus = (BanachSpectrum.comap φ) ⁻¹' d.locus.
```

It uses the actual coefficient-class formulas in the published
`BaseChange.locus_eq_preimage`. These constructions need no completeness of `K`.

Assume `K` complete for all the remaining declarations. `pullbackMap φ d` is
the actual published `presentationTransport` between the two scalar rational
quotients. If `Q_d` is the quotient for `d`, `Q'_d` is that for `pullback φ d`,
and `ι_d,ι'_d` are their structural maps, the module proves

```text
pullbackMap φ d (ι_d(a)) = ι'_d(φ(a)),
(pullbackMap φ d).comp ι_d = ι'_d.comp φ.
```

It also proves that every actual fraction coordinate maps to the fraction with
the same index. The base presentations may have different finite arities,
polyradii and closed ideals; only the rational chart's added coordinates and
radii are retained by this construction.

For an actual chart arrow `h : d ⟶ e`, its bounded restriction is
`h.restriction : Q_e → Q_d`. Compose this with `pullbackMap φ d` to obtain
`α : Q_e → Q'_d`; let `β : B → Q'_d` be the structural map. The stored
over-base equation for `h` and `pullbackMap_comp_baseMap` prove
`α.comp ι_e = β.comp φ`. The actual bounded pushout for the chart `e` now
constructs `Q'_e → Q'_d`. This is the bounded restriction in
`pullbackRestriction φ h`; its structural-map equation is the pushout base
projection. The other pushout projection proves

```text
(pullbackRestriction φ h).restriction.comp (pullbackMap φ e) =
  (pullbackMap φ d).comp h.restriction.
```

Completeness and ultrametricity of `Q'_d` follow from the existing constructed
quotient instances over complete `K`. Thus no boundedness, lifting or target
arrow is assumed as an output object.

`pullbackFunctor φ` has these chosen charts as objects and these constructed
restrictions as maps. Identity and composition are proved by the published
uniqueness of actual restrictions over `B`: target chart generation makes each
arrow type a subsingleton. `pullbackPresheafMap φ` is the natural transformation
from the actual bounded quotient presheaf over `A` to the bounded quotient
presheaf over `B` pulled back along the opposite chart functor. Its components
are `pullbackMap`; naturality is the displayed pushout projection equation.

`pullbackSpectrumMap` is actual continuous seminorm pullback along
`pullbackMap`. `pullbackSpectrumMap_over_base` proves the commuting square with
the coefficient spectrum map by evaluating the coefficient formula on every
base element. The transformation `pullbackSpectrumNat` makes these maps natural
for chart restrictions; its proof evaluates the other pushout projection
equation on every quotient element and every seminorm.

Finally, `pullbackSpectrumCone` is the actual quotient-spectrum cone of the
published base-change construction for the chosen representatives.
`pullbackSpectrumConeIsLimit` applies the published explicit continuous lift
and uniqueness with the source generation stored in `d`. Its vertex is the
actual spectrum of `Q'_d`, and its two legs are the structural map to `M(B)`
and continuous pullback along `pullbackMap` to `M(Q_d)`. It is an `IsLimit`
for this concrete `TopCat` pullback cone.

The original geometric context is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p.8, uses bounded homomorphisms and the dual
direction of affinoid spaces. Exercise 2.2.2(ii), p.9, gives the positive-radius
common-denominator rational quotient and its inequalities. Fact 2.2.3(i),
p.10, identifies a representing-domain spectrum with its domain; Definition
2.2.7 on that page gives the category of affinoid-domain embeddings. These
original pages were read directly; no source-specific errata file is supplied.
The chosen representatives, functor and natural transformations here are
internal constructions from the published concrete quotient results, not
separately named assertions in those passages.

The precise algebraic unit-generation hypothesis is retained. No equivalence
with the source's no-common-zero condition is asserted. Empty added-coordinate
blocks, arbitrary positive radii, trivial valuations, unit ideals, zero
quotients and empty loci are allowed. This module does not prove the full
image-containment factorization property for rational domains, independence
from arbitrary affinoid presentations, coherent comparisons of pullback
functors for different coefficient maps, a Grothendieck topology, a structure
sheaf, an analytic atlas or an etale site.
