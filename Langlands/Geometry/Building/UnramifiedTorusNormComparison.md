# Torus norm comparison with arbitrary splitting fields

Let `F` be a nonarchimedean local field and `K = UnramifiedClosure F` its
inertia fixed field. For affine commutative `K`-groups `T` and `U`, an actual
group-scheme isomorphism `e : T.toGrp ≅ U.toGrp` carries the torus norm
subgroup computed with any finite Galois splitting field `E` of `T` onto
the subgroup computed with any finite Galois splitting field `M` of `U`.
Each valuation is the restriction of the prescribed spectral valuation on
`F`'s separable closure. The field and scheme universe `u` is arbitrary.

`map_torusNormIwahori_eq_of_iso_of_splitting_fields` proves this assertion.
First, base change of `e` shows that `E` also splits `U`. The published
same-field isomorphism comparison carries the norm subgroup for `T` over
`E` to that for `U` over `E`. The local splitting-field independence theorem
then identifies that image with the norm subgroup for `U` over `M`.

`UnramifiedZeroDatum.torusIwahori_map_eq_of_iso` specializes this result to
any two unramified zero data, including data for distinct ambient groups.
The data supply both finite Galois and splitting hypotheses. No equality of
the selected fields, nesting hypothesis, scalar norm-surjectivity premise,
or prior compatibility of their norm images is assumed.
`torusIwahoriEquivOfIso` restricts the actual rational-point isomorphism to
the two norm subgroups. Its coercion formula records that the resulting map
is precisely `rationalPoints.map e.hom`.

This is a derived internal comparison for Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), Definition 2.5.13 and the independence part
of Lemma 2.6.24 (printed p.90 and pp.104–105; PDF p.121 and pp.135–136).
It combines the previously proved norm naturality and local
splitting-field independence. It proves the required torus norm-image
compatibility once an isomorphism of the two tori is supplied; existence of
the sharp conjugator and compatible torus isomorphism remains a separate
geometric obligation.
