# The transport category of actual rational domains

Worker 36 constructed the rational quotient realization. The elementary labelled
category pattern is adapted from Worker 13’s published `ActionOpens`; both
workers are credited in the contribution.

This derived construction works over an ultrametric normed field `K` and a
presented strict affinoid algebra `P`. Objects retain chosen unit-radius rational
presentations. A morphism from `U` to `V` consists of an actual bounded
`K`-algebra automorphism `g` of `P` whose induced point action sends every point
of the source locus into the target locus. Labels remain part of a morphism
even when distinct automorphisms induce the same map on a locus.

The action convention is that `g` acts on points by composition with the
inverse algebra map. Thus the composite of a morphism labelled `g` followed
by one labelled `h` has label `h * g`. The identity has label one. The
`inclusion` functor embeds the ordinary rational inclusion arrows as
identity-labelled arrows. The constructed `translationIso` identifies a
presentation with its translate by the forward algebra automorphism.

For the constructions on quotient algebras, `K` is complete. The source
structural map, composed with the inverse algebra automorphism, has spectrum
image in the target locus. The published rational representation theorem
therefore constructs a unique bounded map from the target quotient algebra
to the source quotient algebra. Its defining equation is
`restriction.comp target.baseMap = source.baseMap.comp label.inv`.
Identity and composition follow from uniqueness and the inverse formula
for products of automorphisms. The spectrum equation states that these
actual quotient-spectrum maps lie over the labelled point action on the
base spectrum.

The restrictions on identity-labelled arrows equal the already published
rational restriction maps. Pullback by the inverse translation arrow equals
the published forward quotient comparison map. These results tie the new
category to both existing restrictions and the actual automorphism action
on quotient sections. The module constructs functors to presented strict
affinoid spaces and their topological spectra, and presheaves valued in
bounded presented algebras and commutative `K`-algebras.

## Provenance and scope

The construction derives from `RationalCategory`, `RationalPullbackProof`,
and `RationalAutomorphism` in the Library. The analogous ordinary-open
transport category is `Langlands.Sheaf.Equivariant.ActionOpens`; rational
presentations here carry different, constructed quotient algebras and are
not identified with ordinary open subsets.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
printed/PDF p. 8, Definition 2.1.11, supplies the contravariant bounded
affinoid morphism convention. Printed/PDF p. 9, Definition 2.2.1 and
Exercise 2.2.2(ii), supplies the rational-domain universal property and
quotient construction underlying the imported strict representation
theorem. The transport category and its coherence are derived
infrastructure, not a source-numbered result.

For the eventual equivariant-site goal, Berkovich's unfinished
*Etale equivariant sheaves on p-adic analytic spaces* (1995–1996),
the retained `Equish_1996` manuscript, printed/PDF pp. 1–3,
sections 1.1–1.2, uses continuous actions on analytic spaces and categories
of equivariant étale or quasi-étale morphisms. This module supplies neither
those sites nor their topology. Section 1.4, printed/PDF p. 7, describes
compatible transport of sections to translated objects, which motivates
the restricted algebra-presheaf construction here. It has no topology on the automorphism
group, no claim of joint action continuity, and no sheaf or descent theorem.
It remains restricted to chosen unit-radius rational presentations over
a single presented strict affinoid algebra.
