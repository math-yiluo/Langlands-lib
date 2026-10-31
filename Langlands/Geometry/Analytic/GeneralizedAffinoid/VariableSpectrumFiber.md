# Actual quotient spectra on the operator-group fibers

This internally derived module restricts the actual quotient-spectrum functor to
the standard fibers of the two operator-group functors. It compares this direct
construction with the existing fixed-group spectrum functor and the constructed
equivalences with fixed-group action categories.

Berkovich's unfinished 1995–1996 manuscript, *Etale equivariant sheaves on p-adic
analytic spaces*, section 1.1, printed/PDF page 3, identifies morphisms with
identity operator-group component as fixed-group morphisms and denotes the fiber
over a group by its fixed-group analytic category. This supplies the convention
and motivation; the precise quotient-spectrum functor and comparisons here are
internal consequences of the existing concrete constructions and Mathlib's fiber
API. Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
PDF member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

`spectrumFiberFunctor G` applies the existing spectrum functor to the underlying
object and morphism in the standard fiber. The strict spectrum/group-forget
square proves that the resulting composite lies constantly over `G`.
`Functor.Fiber.inducedFunctor` then supplies the required equality of object
groups and identity-lift condition on arrows. Composing with the target fiber
inclusion is exactly source fiber inclusion followed by the original spectrum
functor. The object and arrow projection lemmas are definitional equalities.

The existing `ofFixed_comp_spectrumFunctor` is supplemented by
`ofFixedToFiber_comp_spectrumFiberFunctor`, a strict equality of functors.
They retain the original inverse-pullback spectrum action, identity group
homomorphism, and bounded-algebra pullback on seminorms. In particular,
`spectrumFiberFunctor_map_apply` evaluates any fiber arrow as
`x (f.val.algebraMap a)`.

`spectrumFunctor_ofFixedFiberPreimage` verifies that recovering a fixed-group
equivariant arrow from a fiber arrow commutes with taking spectra. Both routes
keep the same continuous seminorm pullback map, and extensionality identifies the
complete fixed-group arrow.

`spectrumFiberComparison` compares the direct functor on standard fibers with
transport of the existing fixed-group spectrum functor through
`fixedGroupFiberEquivalence` on the source and target. The isomorphism comes from
the source equivalence's inverse counit, whiskered with the direct spectrum
functor; the strict compatibility square identifies its target. The direct
functor uses no choice of inverse equivalence. Only the transported description
uses Mathlib's choice-based inverse of the already proved equivalence.

The coefficient field and spectrum spaces have universe `u`, and the bundled
topological group has independent universe `v`. The only field assumptions are
`NormedField` and `IsUltrametricDist`; no completeness, local compactness or
discreteness is added. The source objects remain actual finite
positive-polyradius closed-ideal quotient algebras with norm-continuous orbits,
and the target consists of jointly continuous actions on their actual bounded
multiplicative spectra. General analytic atlases, the comparison with Berkovich's
analytic automorphism topology, and etale and quasi-etale sites remain separate
construction obligations.
