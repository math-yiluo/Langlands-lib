# Discrete and trivial operators on actual quotient actions

This construction realizes the two operator-forgetting arrows of Berkovich's
Example 1.1.3 for the existing category of actual finite positive-polyradius
closed-ideal quotient actions. It also derives their naturality, a
factorization between them and formulas on actual bounded multiplicative
spectra. The group homomorphisms have the source-to-target direction, while the
bounded algebra maps have the opposite direction.

`discreteOperators X` restricts the original quotient action along
`DiscreteOperatorGroup.toOriginal X.groupType`. The discrete copy retains the
original group operations with a separate discrete topology. The original-value
map to the original topological group is continuous because its source is
discrete. Restriction constructs the new continuous algebra-element orbits and
retains the exact original quotient, norm and algebra topology.
`discreteOperatorsMap X` is the canonical restriction arrow, with that
original-value group homomorphism and bounded identity algebra pullback. It is
the quotient version of the source's arrow `a : X(G_d) → X(G)`.

`discreteOperatorsFunctor` retains each original bounded algebra map and
discretizes its original group homomorphism. Equivariance is the original
equivariance equation, since the underlying group elements and operations agree.
The functor laws follow from equality of the retained maps.
`discreteOperatorsNatTrans` gives the canonical arrows `a` as a natural
transformation to the identity functor, again proving naturality by equality of
the group and bounded algebra components.

`trivialOperators P` uses the actual one-element group `PUnit` in the operator
universe and the existing constructed trivial norm-continuous action on the
actual quotient `P`. `trivialOperatorsFunctor` assigns this action to every
opposite quotient object and uses its opposite bounded algebra map on arrows.
`trivialOperatorsMap X` has unit group homomorphism and bounded identity
pullback. Its equivariance follows from the original action homomorphism
preserving the group unit. This is the quotient version of the source's
`b : X({1}) → X(G)`. The maps form `trivialOperatorsNatTrans` from the functor
which forgets the original operators and then supplies the one-element group.
Naturality on group homomorphisms uses preservation of the unit; on algebras it
uses identity pullbacks.

`trivialToDiscrete X` is the same `b` construction applied to the discrete
operator object. It goes from the underlying quotient with trivial operators
to the quotient with discrete operators. Comparing its group and algebra
components proves that composing it with `discreteOperatorsMap X` gives the
entire original `trivialOperatorsMap X`. These intermediate arrows are natural,
and `trivialToDiscreteNatTrans_comp` proves equality of the composite natural
transformation with `trivialOperatorsNatTrans`. These naturality and
factorization assertions are internal consequences of the concrete quotient
category, not additional numbered assertions quoted from the source.

The actual jointly continuous spectrum functor retains the original-value group
homomorphism on `a` and the unit group homomorphisms on `b` and the intermediate
arrow. Each of their space maps is the identity on actual bounded multiplicative
seminorms, proved by evaluation on every algebra element and spectrum
extensionality. The complete spectrum factorization follows from the genuine
spectrum functor's composition law and the established geometric factorization.
No nonempty-spectrum hypothesis is needed.

Source: Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*,
unfinished manuscript (1996), section 1.1, Example 1.1.3, printed/PDF p.3,
with the morphism convention on pp.2–3. Registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf`, member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The two arrows and the meanings of their operator groups come from the source;
their quotient realization and the functorial and spectrum calculations here
are derived from the existing actual quotient category and spectrum functor.

The coefficient field is in universe `u` with only `NormedField` and
`IsUltrametricDist` assumptions; the actual topological operator groups occupy
independent universe `v`. No completeness or nontrivial valuation is assumed.
This construction gives concrete algebraic and topological prerequisites. It
does not identify the norm-orbit continuity condition with the source's full
analytic automorphism topology or construct full analytic atlases, analytic
domains, etale or quasi-etale sites, site morphisms or cohomology.
