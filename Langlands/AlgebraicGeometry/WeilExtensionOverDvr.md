# Weil extension over a discrete valuation ring

`weilExtensionOverDvr` extends an over-base morphism `u` from a fibre-dense
open `U` containing the generic fibre of a smooth quasi-compact scheme `X`
over a DVR to a separated group scheme locally of finite type over the DVR.
The extension is a morphism on all of `X` over the base and restricts to `u`.

On the product of the two copies of `U`, form the group-valued difference
`(x,y) ↦ u(x)u(y)⁻¹`. For any diagonal point of `X × X` over the base, take
an affine open about the associated unit point in the group. The images of
the zero and principal primes of the stalk of `X` at the given point lie
in `U` by `smallPrime_mem`. Their diagonal images have values in this same
affine open, since the difference there is the unit and open sets contain
generizations. `rationalMap_mem_domain_of_affineTrace` puts the diagonal in
the domain of the difference. The factorial stalks on both sides come from
smoothness over the DVR.

Intersect the domain of the difference with the inverse image of `U` under
the second projection. Its first projection is smooth and surjective
because the difference domain contains the diagonal and `U` pulls back to
a dense open in each projection fibre. Quasi-compactness follows from the
Noetherian product. Multiplying the difference by `u` of the second
coordinate extends the pullback of `u` to this cover. The compatibility on
the pullback of `U` is the group identity `(ab⁻¹)b = a`, so the morphism
descends to `X` by `exists_hom_of_agrees_over_dense_open`.

This is the DVR, generic-fibre form of the diagonal argument in Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §4.4 Theorem 1 and Lemma 2,
printed pp. 109–110 (PDF pp. 116–117), with the descent step from §2.5
Proposition 5, printed p. 58 (PDF p. 65). The literature ID is
`bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file SHA-256
is `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
