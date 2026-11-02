# Godement construction from the finite rational chart site's spectrum points

Author: Worker 13.

This is an internal construction from the actual `RationalChart.spectrumPoint`
and filtered stalks, the published `Langlands.Sheaf.Godement` and
`Langlands.Cohomology.CokernelComplex`, and Mathlib's point/skyscraper
adjunction and product universal properties. It supplies the actual family
adjunction and its comparison with the existing Godement construction for this
particular site. No new original-literature theorem is assumed. The general
Godement module records the literature provenance of its cokernel construction;
this module specializes that construction and proves the displayed comparisons.

Fix a complete ultrametric normed field `K : Type u` and a presented affinoid
algebra `A` over it. The site is precisely `finiteRationalTopology K A`: objects
retain chosen finite positive-radius rational data and actual bounded
restrictions, with finite covering families. It is the restricted rational
chart site over one affinoid, without an identification with the full analytic
or etale site.

Let `E : Type uE` have hom universe `vE`, products indexed by types in `u`,
and colimits of size `(u,u)`. These are the explicit hypotheses throughout the
family-adjunction and unit constructions. They permit the individual
membership-indexed skyscrapers and the product over `BanachSpectrum A`, as
well as the actual filtered stalk colimits. The coefficient object and hom
universes are independent of the field universe. No finite-limit, AB5,
concrete-category, abelian or sheafification assumption is needed in this part.

`CoefficientSheaf E` is the category of actual `E`-valued sheaves on this site.
`stalkFamily E` sends a sheaf to the family of its already constructed stalks,
indexed by every actual `x : BanachSpectrum A`, and a morphism to its family of
stalk maps. `skyscraperFamily E` sends a coefficient family `M` to the categorical
product of the actual point skyscrapers of `M x`; its morphisms are the induced
product maps. These use Mathlib's category of indexed families, `Functor.pi'`,
`Functor.pi` and the product functor.

`familyHomEquiv F M` constructs the natural bijection

`Hom(stalkFamily(F), M) ≃ Hom(F, skyscraperFamily(M))`.

A family of stalk maps is sent through each individual stalk/skyscraper
adjunction and assembled by the product universal property. Conversely, a map
into the product is projected to each skyscraper and sent through the inverse
individual adjunction. Projection identities and the individual bijection
identities prove that these constructions are inverse. Naturality on the left
follows componentwise from the individual adjunctions; naturality on the right
also uses the product-map projection identity. `familyAdjunction` is the
resulting actual adjunction.

`zeroFunctor E` and `coaugmentation E` specialize the published Godement
endofunctor and its unit to this complete spectrum-point family. The existing
endofunctor is a product in a functor category. `zeroFamilyIso E` identifies it
naturally with `stalkFamily E` followed by `skyscraperFamily E`: its components
are Mathlib's `piObjIso`, evaluating a product of functors. Naturality is proved
by composing with each product projection and using naturality of that
projection. `familyAdjunction_unit_π` identifies each component of the family
unit with the individual adjunction unit. `coaugmentation_zeroFamilyIso` then
proves that the existing Godement coaugmentation is exactly this family unit
under the natural product comparison.

`zeroProjection F x` is the projection from degree zero to the skyscraper of
the stalk at `x`. `coaugmentation_zeroProjection` computes the composite with
the coaugmentation. Given a chart `d` and `hx : x ∈ d.locus`,
`coaugmentation_germ` further projects the underlying sections to the factor
indexed by this actual membership. The result is exactly `germ x d hx F.obj`.
The proof specializes the individual adjunction's explicit presheaf product
formula to the identity of the stalk; the final composite with that identity
is the original colimit germ map.

`stalkRetraction F x` first applies the stalk at `x` to `zeroProjection F x`
and then applies the individual adjunction counit. The identity
`coaugmentation_stalkRetraction` proves that it retracts the stalk map of the
Godement coaugmentation, by functoriality and the individual adjunction's left
triangle identity. This splitting is a statement on each constructed stalk;
it does not assert that these stalks detect monomorphisms of sheaves.

For the final complex constructions, `E` is additionally abelian and has the
explicit `HasSheafify (finiteRationalTopology K A) E` instance. The actual sheaf
category is then abelian. `complexFunctor E` specializes the existing functorial
Godement cokernel complex, and `complex E F` is its value on a sheaf. Concretely,
starting with the identity residual functor, each next residual is the
categorical cokernel of its coaugmentation; the degree-n term applies
`zeroFunctor E` to the nth residual. Each differential is the cokernel
projection followed by the next coaugmentation. The published construction
proves that these differentials compose to zero and defines the induced maps
of complexes. `augmentation F` is the original coaugmentation into degree zero;
`augmentation_d` gives its zero composite with the first differential.

No conservative or enough-points family, monic coaugmentation, exact or acyclic
resolution, compact-support condition, smooth equivariance, arithmetic
coefficient system, Harris tower or analytic/etale comparison is asserted.
The complex is a constructed cochain complex, without an exact-resolution claim.
The inherited chart framework allows trivial valuations, nilpotents and empty
loci. There is no nonemptiness assumption on `BanachSpectrum A`; all family
constructions use ordinary categorical products, including the empty product.
