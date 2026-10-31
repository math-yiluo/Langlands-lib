# Actual quotient spectra with varying topological operator groups

`VariableActionSpace K` retains a topological group and a norm-continuous action
on an actual positive-polyradius closed-ideal quotient. Its morphisms have the
geometric direction: a continuous homomorphism from the source group to the
target group and a bounded `K`-algebra map from the target algebra to the source
algebra, with the stated equivariance equation.

Identity and composition are constructed from these actual maps. The algebra
maps compose contravariantly. Their extensionality proves the category laws.
`restrictedAlgebraHom` recovers the corresponding existing fixed-group algebra
arrow after restriction of the target action. `ofFixed` faithfully embeds the
existing opposite fixed-group action category using identity group maps.

`spectrumFunctor` constructs actual bounded multiplicative spectra with the
previously derived jointly continuous actions. On an arrow with algebra map `f`,
the map of points is `x ↦ (a ↦ x (f a))`, and its group map is the original
continuous group homomorphism. Equivariance follows by applying the algebraic
equivariance equation to the inverse source-group element, using preservation of
inversion by the group homomorphism, and evaluating the resulting equality with
the seminorm. The functor laws follow on seminorm evaluations. Forgetting the
operators agrees exactly with the existing non-equivariant spectrum functor.

The field `K : Type u` is an ultrametric normed field; the groups occupy an
independent universe `v`. There is no completeness or nontrivial valuation
assumption. The topological groups and their continuous homomorphisms, quotient
algebras, bounds, actual norms and continuous spectrum maps are retained.

The source motivation is Berkovich's unfinished *Etale equivariant sheaves on
p-adic analytic spaces* (1996), section 1.1, printed/PDF pp.2–3: its category of
spaces with operators has a continuous source-to-target group homomorphism and
a compatible geometric map. The fixed-group arrows use the identity group
homomorphism. Registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf`, member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The exact quotient construction and functor here are internally derived from
the published `NormContinuousAction` and actual spectrum APIs, rather than
attributed to a numbered theorem in the manuscript.

This is a fixed-field algebraic and topological prerequisite. It does not
identify continuous norm orbits with the manuscript's topology on analytic
automorphisms, construct its varying-field analytic category, or assert an
analytic atlas, etale or quasi-etale site, covering or cohomological comparison.
