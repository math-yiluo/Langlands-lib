# Laurent coordinates of invariant cocharacters

Worker 1272.

This derived construction supplies the coordinate part of the descent step in
Milne, *Algebraic Groups* (2017), Theorem 25.1, printed page 544 (PDF page 560).
Its mathematical inputs are the existing actual cocharacter transport,
representation of the multiplicative group by relative Laurent spectra, affine
coordinate presentations, and finite Galois descent of Laurent coefficients.
It does not assume a parabolic classification or a cocharacter descent theorem.

Let `k` and `K` be fields in the same universe with a `k`-algebra structure on
`K`, and let `G` be a group scheme over `Spec k`. The maps `extendAlg` and
`conjugateAlg` extend and conjugate Laurent coefficients while retaining the
`k`-algebra structure. The Laurent test, universal point, and explicit changes of
base structure identify the geometric action with coefficient conjugation.
`universalProjection_transport` proves this comparison for the point projected
from the base change of `G` to `G`.

For affine `G`, `coordinates` evaluates a cocharacter of `G_K` at the universal
Laurent unit and writes its image in the chosen affine coordinate algebra of
`G`. The proposition `IsInvariant` means invariance under every instance of the
published `transportCocharacter` for `Gal(K/k)`.
`coordinates_fixed` proves that every Laurent coordinate of an invariant
cocharacter is fixed by coefficient conjugation. The proof first uses invariance
in the projected-point comparison, then applies naturality of affine
coordinates. The intermediate comparison `universalValue_of_projection` only
uses two arbitrary cocharacters and a comparison of their projected points.

If `K/k` is also finite dimensional and Galois, `descendedCoordinates` applies
`LaurentGaloisDescent.descendAlgHom` to these invariant coordinates.
`descendedPoint` uses the inverse affine-coordinate equivalence to obtain an
actual point over `k[T,T⁻¹]`. The theorem `extend_descendedPoint` says that
extending this point's coefficients to `K` recovers the original cocharacter's
universal value. Its proof applies the injective coordinate equivalence and the
coefficient-extension identity of `descendAlgHom`.

`descendedMorphism` composes this Laurent point with the canonical Laurent
presentation of the actual multiplicative group over `k`, obtaining a morphism
of schemes over `Spec k`. `laurentPoint_descendedMorphism` records its value on
the universal point. This module does not yet identify the base change of this
scheme morphism with the original cocharacter or prove that it respects the
group laws. Those are the remaining geometric steps to a descended group-scheme
homomorphism. No finite type, smoothness, reductivity, perfectness, or
characteristic assumption is used in this coordinate construction.

The universal Laurent point is reused as `Gm.laurentPoint` from
`GroupScheme.Torus.Lattice`, with the same inverse relative-Laurent isomorphism.
