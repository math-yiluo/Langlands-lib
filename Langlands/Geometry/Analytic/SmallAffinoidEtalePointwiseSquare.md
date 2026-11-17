# Small affine étale squares at a prescribed ordinary point

This internal construction takes the open étale part of the actual small
affinoid pushout. The first bounded map `f : A → B` is finite Banach and is
étale at the prescribed ordinary source point. The map `g : A → C` is an
arbitrary bounded map. The three original spectra are small in the supplied
space universe, independently of the field universe. The finite Banach
pushout and finite tensor comparison propositions remain explicit premises.

`etalePushout` is the actual analytic open domain in the finite small pushout
where the original second bounded leg is pointwise étale. Its inclusion and
two projections are the actual strong morphisms from the domain inclusion and
the original bounded pushout maps. Associativity and the original pushout
equation prove equality of their entire strong composites.

`etalePushoutSnd_etale` applies `SmallAffinoidEtaleNeighborhood` to the finite
second leg. It supplies the exact localized étale predicate used by the
analytic étale site for the restricted projection.

For compatible prescribed ordinary points, the full affinoid pushout supplies
a spectrum point over both of them. The finite tensor comparison transfers
pointwise étaleness of `f` at the prescribed source point to the second leg
at this lifted point. The point therefore belongs to the open source above.
The small-spectrum homeomorphism and the original projection identities give
the prescribed ambient point equalities. This proves
`exists_etale_pointwiseSquare_of_finite` with no global étaleness premise.

The result concerns bounded maps of affinoid algebras with a finite first leg.
It does not yet construct the required finite local models of arbitrary
analytic étale maps, or prove unrestricted site-level pointwise lifting.
