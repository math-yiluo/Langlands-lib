# The represented dynamic parabolic as a product of schemes

This is a derived construction from the published dynamic limit theory in
`Dynamic.LimitMap` and the all-test representability interface in
`RepresentedSubgroup`. It does not introduce a new classification result.

Let `G` be a separated group scheme over any scheme `S`, and let
`χ : Gm S → G` be a cocharacter. For actual representatives `iZ`, `iU`, and `iP`
of the intrinsic subgroup functors `centralizer χ`, `unipotent χ`, and
`parabolic χ`, respectively, `parabolicProductIso` constructs an isomorphism
of schemes over `S`

`Z.X ×_S U.X ≅ P.X`.

Its forward map is multiplication in `G`, as recorded by
`parabolicProductIso_hom_comp`. This is an isomorphism of underlying schemes:
the direct-product group law on the source need not make multiplication a
group homomorphism.

The implemented proof applies the Yoneda bijectivity criterion to the
multiplication morphism factored through `P`. For every test scheme, the limit
of `z * u` is `z`; uniqueness of limits for separated `G` gives injectivity.
For a parabolic point `g`, its unique limit `l` lies in the centralizer and
`l⁻¹ * g` lies in the unipotent functor. Representability factors these two
points through `Z` and `U`, giving surjectivity on every test scheme. No
smoothness, affineness, field, or reductivity hypothesis is used.
