# Affine scheme pushouts from ring pullbacks

`Langlands.AlgebraicGeometry.affineSchemePushout` proves exactly the published
`Langlands.AlgebraicGeometry.AffineSchemePushoutStatement.{u}`. For arbitrary
`A B C D : CommRingCat.{u}` and the actual displayed maps `f`, `g`, `i`, and
`j`, its only premises are surjectivity of `f.hom` and `IsPullback i j f g`.
The conclusion is `IsPushout (Spec.map f) (Spec.map g) (Spec.map i) (Spec.map j)`
in the full category `Scheme.{u}`. In particular, the universal property permits
arbitrary scheme targets in that universe. The proof preserves the published
statement and its imports.

The implemented proof first treats the compatible-pair ring
`P = f.hom.pullback g.hom`, with its actual first and second projections.
`isPushout_specPresheafedSpace` proves that the corresponding square of
presheafed spectra is a pushout. The commuting square follows from
`RingHom.pullback_comm_sq` and contravariant functoriality of the spectrum.
The general construction `isPushout_presheafedSpace` then combines two inputs.

The topological input is `isPushout_comap_pullback`, proved in
`AffineSchemePushoutTopology`. Surjectivity of `f.hom` is used there to prove
joint surjectivity of the two spectrum maps, the final topology, and the
required identification of their fibers. Compatible continuous maps consequently
descend uniquely to the pullback spectrum.

The presheaf input is `isPullback_specPresheaf`, from
`AffineSchemePushoutSectionMaps`. It identifies the actual pushed spectrum
section maps, including the equality transport in the second map, with the
presheaf square established in `AffineSchemePushoutSheaf`. The latter square
is proved on each prime-spectrum basic open by localization of ring pullbacks;
the sheaf basis criterion makes the global comparison an isomorphism.
No surjectivity is needed for this sheaf input.

The general presheafed-space construction descends the continuous map through
the topological pushout and lifts its compatible presheaf maps through the
pushed presheaf pullback. These two universal properties also prove the
factorization equations and uniqueness. This supplies the universal property
against every presheafed-space target, without an affine or sheaf restriction.

`isPushout_specLocallyRingedSpaceMap_canonical` reflects that pushout through
the sheafed-space and locally ringed-space forgetful functors using
`AffineSchemePushoutLifting`. The sheafed-space forgetful functor is fully
faithful. For locally ringed spaces, Mathlib provides colimits, preservation
of colimits by the sheafed-space forgetful functor, and reflection of
isomorphisms; together these imply reflection of the required colimit.
Reflection through the fully faithful scheme forgetful functor gives the
canonical pushout in all schemes.

Finally, `isPushout_specMap_of_canonical`, from
`AffineSchemePushoutTransport`, compares the supplied ring pullback `A`
with `P` by uniqueness of limits. Its two projection equations show that
transporting the canonical scheme cocone gives precisely the supplied maps.
The final theorem applies this transport to the canonical scheme pushout.
There is no affine-target, reducedness, nontriviality, separation, integrality,
or finite-type premise added to the published target.

For downstream constructions,
`AffineSchemePushout.isPushout_specLocallyRingedSpaceMap` exposes the same
result for the arbitrary supplied ring pullback in locally ringed spaces.
It uses the same canonical result and contravariant transport. This is a
proved consequence of the construction, not an extra premise in the exact
scheme theorem. Global scheme gluing, conductor and contained-ideal
comparisons, affine-neighborhood preservation, and Picard representability
remain separate tasks.

Worker 1568 implemented the localization, sheaf comparison, general
presheafed-space criterion, and final assembly. Worker 336 implemented the
topology, section-map comparison, categorical lifting, and transport modules.
Worker 1764 contributed the categorical lifting route. The proof follows the
constructed Lean universal properties described here.
