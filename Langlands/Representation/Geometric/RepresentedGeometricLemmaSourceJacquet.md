# The source-intersection Jacquet quotient

This is an internal adapter for the local normalized orbit calculation on
arbitrary represented parabolics. It uses the canonical topologies on the
groups' own rational points and keeps the group and coefficient universes
independent. The generic character comparison needs an affine ambient group
with locally compact, nonarchimedean rational-point group over a Hausdorff
topological field. The specialization uses the original nonarchimedean local
field and geometric-lemma intersection datum.

`leviRestrictionCharacter` restricts a smooth ambient character along the
original map of the represented Levi into the ambient group. Its open kernel
is the preimage of the original open kernel through the continuous Levi
point-image equivalence followed by subgroup inclusion.

For a smooth character `χ` explicitly assumed trivial on the actual radical
point image, `leviJacquetTwistIso` gives a natural isomorphism between twisting
before normalized Jacquet restriction and twisting afterwards by that
restriction character. The underlying linear equivalence is
`Jacquet.Localization.transportEquiv`, using the identity maps on the radical
and coefficient module. Triviality of `χ` on the radical makes the two sets of
coinvariant relations agree. On a representative class, the map sends `[a]`
to `[a]`, as recorded by `leviJacquetTwistIso_hom_mk`.

The normalized action contributes the same inverse half Haar scalar on each
side. Commuting that scalar with `χ` proves intertwining on representative
classes, which generate the entire quotient. Intertwiners between source
representations act by their original linear maps on these representatives,
so the same description proves naturality on the full smooth category.

For the original datum `D`, `sourceRadical_le_ker_inducingHalfCharacter` proves
that the original source inducing half-character is trivial on the radical
of `D.p'`. This is the actual image of `D.r'` in the source Levi's own points,
not the radical of the original source parabolic. The positive Haar character
of the original source radical, restricted to the source Levi, has open
kernel. The published
`isLimitOfCompactSubgroups_pointImage_radical` places every compact subset of
the intersection radical in a compact subgroup.
`positiveCharacter_eq_one_on_compactLimit` therefore makes that positive
character equal to one on the intersection radical; taking its positive
square root and embedding into complex units gives the asserted triviality.

`D.sourceJacquetInducingHalfTwistIso` applies the generic comparison with
`D.p'`, `D.l'`, `D.r'` and the original `leviInducingHalfCharacter`. The kernel
premise is discharged by the preceding theorem. The output character is the
original inducing half restricted along `D.l' ≫ D.p'`.
`sourceJacquetInducingHalfTwistIso_hom_mk` states its identity formula on
quotient classes. The affine, locally compact and nonarchimedean structures
on the original source Levi are supplied by its existing rational-point
equivalence with the literal closed Levi image.

The provenance is internal: the quotient transport, original Haar character,
represented Levi point equivalences and radical compact-subgroup theorem are
existing Library constructions and results. This unit derives their natural
compatibility. It assumes no standardness, chosen roots, dynamic presentation,
representation finiteness or distinct-radical modulus equality.

The full orbit-stabilizer calculation, quotient integration and remaining
normalization cancellation are separate obligations. This adapter does not
prove `RepresentedGeometricLemmaOrbitComparisonStatement`.
