# Coherent comparisons for chosen rational chart pullbacks

Author: Worker 56.

This module constructs identity and composition comparison isomorphisms for
the published coefficient pullback of actual positive-radius rational charts.
It is internally derived from the published representative maps, coefficient
transport and uniqueness of actual restrictions. All quotient algebras and maps
are the concrete ones in those constructions.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.
Fix an ultrametric normed field `K` and presented affinoid algebras
`A,B,C,D`. A chart includes finite rational data, positive radii and unit
generation of its denominator and numerator classes.

The identity-pullback class formulas show that the chosen denominator and
numerators represent the original classes. The comparison `pullbackIdIso d`
has source `pullback (BoundedAlgHom.id K A) d` and target `d`. Its forward
arrow is represented contravariantly by the actual bounded
`representativeMap` from the quotient of `d` to that of its chosen identity
pullback. Its inverse uses the reverse representative map. Each over-base
equation follows from `representativeMap_baseMap`. Published uniqueness of
actual restrictions proves the two inverse laws.

For arbitrary bounded maps `φ : A → B` and `ψ : B → C`, the direct and iterated
pullbacks keep exactly the same finite arity and positive radii. Their
denominator classes agree because both are `ψ(φ(q_A(g)))`; the numerator
class formulas have the same proof. The isomorphism `pullbackCompIso φ ψ d`
goes from `pullback (ψ.comp φ) d` to `pullback ψ (pullback φ d)`. Its forward
arrow is the representative map from the iterated quotient to the direct
quotient; its inverse uses the reverse map. Their base equations and inverse
laws follow as in the identity case. These object isomorphisms and class
formulas do not require completeness of `K`.

Assume `K` complete for the functors and quotient transport below. The existing
functor on actual chart restrictions then supplies `pullbackIdNatIso` and
`pullbackCompNatIso`, respectively

```text
pullbackFunctor id ≅ identity,
pullbackFunctor (ψ.comp φ) ≅ pullbackFunctor φ ⋙ pullbackFunctor ψ.
```

Their components are exactly the constructed object isomorphisms. Naturality
uses the proved subsingleton property of actual restriction types, whose
existence here comes from the representative maps and the published pullback
functor.

The comparison maps agree with the previously constructed quotient transport.
`pullbackIdIso_hom_restriction` identifies the forward identity comparison
with `pullbackMap id d`. If `c` is the forward composition comparison,
`pullbackCompIso_hom_transport` proves

```text
c.restriction.comp ((pullbackMap ψ (pullback φ d)).comp (pullbackMap φ d))
  = pullbackMap (ψ.comp φ) d.
```

Both proofs use generated-base extensionality on the source quotient.
The identity equation compares the structural-map equations. The composition
equation evaluates both sides on every base element and applies the two
coefficient transport formulas and the comparison's over-base equation.
Evaluating these bounded-map equalities at every quotient element and every
multiplicative seminorm proves the stated identity and composition equations
for the actual continuous spectrum maps.

The pointwise coherence equations `pullbackCompIso_source_id` and
`pullbackCompIso_target_id` say that comparison with an identity map, followed
by the corresponding identity comparison, gives the identity chart arrow.
`pullbackCompIso_assoc` equates the two comparison paths from direct pullback
along three successive coefficient maps to the triply iterated chart. These
are equations of actual chart arrows. The unit and associativity equalities
of bounded coefficient-map composition are definitional; uniqueness of
restrictions proves the resulting path equalities. Together with naturality,
these provide coherent identity and composition comparisons, without
introducing a separate bundled pseudofunctor.
The target-identity equation only uses the object comparisons and therefore
does not require completeness of `K`.

The source context is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p.8, specifies bounded homomorphisms and the
dual direction of affinoid spaces. Exercise 2.2.2(ii), p.9, supplies the
positive-radius common-denominator rational quotient and inequalities;
Fact 2.2.3(i) and Definition 2.2.7, p.10, give the representing-domain
spectrum identification and affinoid-domain embeddings. The comparison
isomorphisms, naturality and coherence equations here are internal
consequences of the published concrete quotient constructions, rather than
separately numbered assertions in those passages. The original pages were
read directly; no source-specific errata file is supplied.

The algebraic unit-generation condition is retained without claiming its
equivalence to the source's no-common-zero wording. Arbitrary positive radii,
empty coordinate blocks, trivial valuations, unit ideals, zero quotients and
empty spectra are allowed. The module provides no general factorization
from image containment, arbitrary-presentation independence, covering
preservation, structure sheaf, analytic atlas or etale site.
