# Polarized smooth proper representability over affine bases

`PolarizedSmoothProperEtaleDescentStatement.{u,v}` is the following
effective descent proposition. Let `S` and `U` be affine schemes in
universe `u`, and let `p : U → S` be surjective and étale. Let
`F : (Over S)ᵒᵖ ⥤ Type v` be a sheaf for the big étale topology on the
slice. Supply a `PresheafLineBundle F`: actual line bundles on all
families, with cartesian isomorphisms satisfying the identity and
composition laws.

Suppose that the base-restricted presheaf is represented by a scheme
`M → U` which is smooth and proper, and that its universal line bundle,
obtained by evaluating the supplied coherent data on the universal
family, is ample. Then `F` is represented by an actual scheme `N → S`
which is smooth and proper and whose universal line bundle from the
same coherent data is ample. The conclusion includes the representing
equivalence, with its naturality for every test scheme. The value
universe `v` is independent of `u`; in particular, `v = u + 1` is allowed.

The hypotheses concern a local representing scheme and a line bundle on
the presheaf. They do not supply a global representing scheme, a global
scheme descent datum known to be effective, or a global polarization.
The coherent bundle supplies the actual isomorphisms needed to descend
the local polarization together with the local representing scheme.

This is a derived specialization of the Stacks Project's stack property
for polarized proper schemes: Section 99.14, Situation 99.14.1 and
Lemma 99.14.3, tag
[0D1L](https://stacks.math.columbia.edu/tag/0D1L).
That source uses proper flat finitely presented morphisms and relatively
ample invertible sheaves, with cartesian scheme morphisms and actual
line-bundle isomorphisms. Smooth proper morphisms meet those geometric
hypotheses. Here the source and target of the base cover are affine,
so the given étale cover is an fppf cover and absolute ampleness is
equivalent to relative ampleness over the respective affine base.
Definition 29.38.1, tag
[01VH](https://stacks.math.columbia.edu/tag/01VH), supplies the
relative-ampleness convention. Lemma 74.13.1, tag
[0D3C](https://stacks.math.columbia.edu/tag/0D3C), is the source's
fpqc descent result for relative ampleness.

To obtain the presheaf formulation, local representability determines the
overlap scheme isomorphism and its cocycle by Yoneda. The coherent bundle
identifications give the compatible polarization on these overlaps.
Effective polarized descent supplies a scheme; the étale sheaf condition
then identifies its functor of points with `F`. Smoothness and properness
descend, and relative ampleness descends on the base. This explains the
provenance of the proposed statement; this module does not implement
that proof.

The original HTML for the three cited tags is retained in registered
source `stacks-polarized-proper-descent-2026-11-14`, snapshot accessed
2026-11-14, content SHA-256
`b9443e52779eaea7a6c238da47a6195e173e2c6bc8a0bf88a47bd0b892b73e19`.
This proposition is a general descent prerequisite. Application to the
parabolic presheaf still requires construction of its coherent
polarization and of a smooth proper local representer with ample
universal bundle.
