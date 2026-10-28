# Subgroup change on finite invariant rational sites

This is a derived local construction from the published invariant rational site
and subgroup-restriction interfaces. It proves continuity of the existing actual
subgroup-change functor and constructs its ordinary precomposition functor on
sheaves.

The base field `K` is a complete ultrametric normed field, `P` is an actual
presented strict affinoid algebra over `K`, and `ρ` is a `RationalSpectralAction`
of a topological group `G` on `P`. The field and group have independent universes.
For open subgroups `V ≤ U`, the functor `invariantRestrictionFunctor` sends a
`U`-invariant rational domain to the same rational presentation with its proved
`V`-invariance. Its morphisms retain the original inclusions and actual bounded
restriction maps.

## Whole domains and intersections

`invariantRestriction_whole` and `invariantRestriction_inter` identify the
restricted whole and intersection objects exactly with the previously constructed
whole and intersection objects for `V`. They retain the actual quotient
presentations, including the product-denominator intersection.

`invariantRestrictionInterLift` takes inclusions from any `V`-invariant source
into two restricted `U`-invariant domains and constructs the inclusion into their
restricted intersection. Its source need not be `U`-invariant. The lift is the
existing actual rational intersection inclusion, wrapped in the invariant full
subcategory. Thinness of this inclusion category gives the required equations
and uniqueness. This constructs the image pullback cone's universal property
and proves that subgroup restriction preserves terminal objects and pullbacks
of inclusions.

## Finite covers and their reflection

`invariantRestriction_isFiniteCovering_pushforward` takes the original finite
covering family in a sieve and uses its image family. The loci are unchanged,
so the image sieve covers for the finite invariant rational topology.

Conversely, `invariantRestriction_isFiniteCovering_of_pushforward` takes a
finite covering family in the image sieve. Each of its arrows factors through
an image of an original sieve arrow. Choosing one such factorization for each
member gives finitely many original sieve arrows. Each original domain contains
the locus of the corresponding covering domain, so those original domains cover
the original target. The proof uses only finiteness of the chosen covering family,
not that every `V`-invariant domain is `U`-invariant.

`invariantRestriction_pushforward_mem_iff` records preservation and reflection
of covering for every original sieve. `invariantRestriction_coverPreserving`
packages preservation as Mathlib's `CoverPreserving`.
`invariantRestriction_ofArrows_mem_iff` also compares the generated sieves of a
finite family and its image family directly. Cover index types lie in the field
universe, as in the published topology; empty families and empty loci are allowed.

## Continuity and sheaves

`invariantRestriction_compatiblePreserving` uses the intersection lift above to
prove Mathlib's compatibility-preserving condition. A compatible family on the
original site can be compared on the original intersection. Pulling that equality
back along the constructed lift gives equality on any comparison domain of the
smaller-subgroup site. Thus comparisons through domains outside the image of the
functor are included.

Mathlib's `Functor.isContinuous_of_coverPreserving` combines this condition
with cover preservation to prove `invariantRestriction_isContinuous`.
`invariantSheafRestriction` then uses the standard
`sheafPushforwardContinuous` construction. For any coefficient category `A`, it
sends sheaves on the `V`-invariant rational site to sheaves on the `U`-invariant
rational site. Its underlying presheaf is exactly precomposition with the
opposite of the subgroup-change functor, as `invariantSheafRestriction_obj`
states. Coefficient objects and homs have independent universes, also independent
of `K` and `G`.

This constructs a functor on already given sheaves. It asserts no sheaf property
for the actual quotient-algebra presheaf and no existence of a structure sheaf.

## Provenance and scope

Berkovich's unfinished 1995–1996 manuscript, *Etale equivariant sheaves on p-adic
analytic spaces*, section 1.1, printed/PDF pp.2–3, defines continuous group actions,
equivariant maps, and morphisms with a continuous homomorphism between acting
groups. Section 1.2, printed/PDF p.3, defines equivariant etale and quasi-etale
coverings using the underlying geometric covering families and describes the
associated site and sheaf functoriality. Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF digest
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Those passages motivate this construction; they do not state this restricted
finite rational-site theorem verbatim. The actual rational quotient objects,
bounded restrictions, locus covers and continuous spectrum actions here are
the published `InvariantRationalSite` and `InvariantSubgroupRestriction`
constructions. The new proofs use their actual intersections and unchanged loci,
and the generic site constructions in Mathlib's
`CategoryTheory/Sites/CoverPreserving.lean` and
`CategoryTheory/Sites/Continuous.lean`. The local compatibility proof follows the
existing `RationalContinuity` construction, adapted to the invariant full
subcategories and subgroup change.

This is a fixed-field, unit-radius rational construction for the published
restricted rational spectral action. It does not construct arbitrary analytic
atlases, etale or quasi-etale morphisms or sites, induced analytic spaces,
scalar descent, Tate acyclicity, or cohomology.
