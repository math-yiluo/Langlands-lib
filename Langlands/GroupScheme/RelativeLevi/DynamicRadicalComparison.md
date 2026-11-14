# Comparing relative radicals of a represented dynamic parabolic

This internal construction connects an ambient dynamic presentation to
`RelativeLevi.dynamicRadicalIso`. It works over an arbitrary base scheme `S`
in any universe. It constructs compatible comparisons from supplied relative
radicals; it does not assert their existence or construct an etale cover.

`Dynamic.parabolicCocharacter` lifts an ambient cocharacter `chi` into any
representative `iP : P → G` of its dynamic parabolic. The published
`Dynamic.range_le_centralizer` puts the image of `chi` in its centralizer,
which lies in the parabolic. Factoring through the representative gives an
actual group-scheme homomorphism `Gm → P`.
`parabolicCocharacter_comp` states that its composite with `iP` is `chi`.

`Dynamic.isRepresentedBy_unipotent_parabolic_factor` assumes that `iP` is
closed, a cocharacter `chiP` lifts `chi`, `iU : U → G` represents the ambient
identity-limit subgroup, and `r : U → P` factors `iU`. The ambient identity-limit
subgroup lies in the parabolic on every test scheme. Thus the range of `r` is
the inverse image of that subgroup along `iP`. The published closed-subgroup
restriction identity identifies this inverse image with the identity-limit
subgroup for `chiP`. Monicity follows from that of the ambient representative
`iU`. These are exactly the two fields of `IsRepresentedBy`.

`RelativeLevi.dynamicParabolicRadicalIso` assumes that `G` is affine and locally
of finite presentation over `S`, that `iP` and `iU` are the supplied dynamic
representatives, and that both `n : N → P` and the compatible factor
`r : U → P` satisfy the full `IsRelativeUnipotentRadical` predicate.
Arbitrary-base dynamic representability and transport between representatives
make `iP` closed. Consequently `P` is affine over `S`. The preceding lift and
restriction lemma supply the hypotheses of `dynamicRadicalIso`, which produces
`N ≅ U`. `dynamicParabolicRadicalIso_hom_comp` proves that its homomorphism
composed with `r` is `n`.

The construction uses equality of subgroup functors on all relative test
schemes, including nonreduced schemes. It imposes no field, reducedness,
noetherianity or affineness condition on `S`. Its provenance is the categorical
composition of the published factorization, closed restriction and dynamic
representability interfaces with the dynamic radical rigidity construction.
It supplies an internal adapter for the local comparison step motivated by
Conrad's relative radical theorem, rather than a transcription of a further
source theorem. Global existence, etale-local dynamic presentations and descent
remain separate obligations.
