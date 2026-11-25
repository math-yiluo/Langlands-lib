# Group-isomorphism schemes for generically isomorphic reductive DVR groups

`GenericIsomorphismSchemeExistenceStatement` asserts the following in every
universe `u`. Let `R` be a commutative domain that is a discrete valuation
ring, let `K` be its specified fraction field, and let `G` and `H` be
reductive group schemes over `Spec R`. Every actual generic-fibre
isomorphism `f` implies the existence of a `GroupIsomorphismScheme G H`.
The representing scheme classifies all actual natural local isomorphism
families on every relative test scheme. It represents the entire
isomorphism functor, rather than a subset selected using `f`.

The supplied-data interface includes a universal natural family and a
bijective refinement map on every test. By the published
`LocalGroupIso.baseChangeIsoEquiv`, these families are exactly actual
isomorphisms of the base-changed group schemes. No finite type,
quasi-compactness, affineness, section, or outer quotient assertion is
included in this proposition.

This is a derived application of Brian Conrad, *Reductive group schemes*
(2014), Theorem 7.1.9(1), pp.245–247, and the forms argument in the proof
of Theorem 7.2.16, p.261. The original is retained as source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Theorem 7.1.9 represents the automorphism functor of a reductive group
over an arbitrary base and proves its properties by étale descent.
The Isom application proceeds by the same descent after identifying `G`
and `H` étale locally. Over a DVR, their geometric root data are locally
constant, and the generic isomorphism identifies them; the isomorphism
theorem therefore makes them étale forms of each other. The resulting
Isom sheaf is a form of the represented automorphism scheme and is
representable. This descent and the passage to the all-test
`GroupIsomorphismScheme` interface remain proof obligations here.

Conrad's final local-field isomorphism theorem additionally uses a
henselian base and finite residue field to trivialize torsors. This
proposition asserts only representability, before that step, over every
DVR. It assumes no henselianity, completeness, splitting, characteristic,
or residue-field finiteness. It is a proposition-valued definition and is
not proved by this module.
