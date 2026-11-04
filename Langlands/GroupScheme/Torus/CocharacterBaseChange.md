# Actual diagonalizable homomorphisms under purely inseparable base change

This module is an internal construction from the actual affine-point,
diagonalizable-group, coefficient-descent and scheme-pullback APIs. It works
in an arbitrary common universe `u`. All fields, exponent groups and test
algebras occurring in a declaration have that universe.

For a commutative group scheme `Z` over a field `k` and an additive abelian
group `Λ`, write `D_k(Λ)` for
`Diagonalizable.groupScheme (CommRingCat.of k) Λ`. The predicate `IsMult`
is the existing equality between the diagonal exponent map of a point and
the product of its two coordinate exponent maps. These are actual points
on spectra of group algebras.

## Universal points and actual homomorphisms

`IsMult.postcomp` proves that a group-scheme homomorphism preserves this
predicate. Applying its homomorphism on affine points to the multiplicativity
equality proves the result; naturality of precomposition gives the desired
equality for the composite point. No affineness or finite type assumption
is needed for this lemma.

`isMult_diagonalizable_id` proves multiplicativity of the identity point of
`D_k(Λ)`. The diagonalizable corepresentation identifies this equality with
an equality of characters into units. Evaluation on each exponent reduces
it to `X^(m,m) = X^(m,0) * X^(0,m)` in the product group algebra.

`pointOfHom f` is the underlying scheme map of an actual homomorphism
`f : D_k(Λ).toGrp ⟶ Z.toGrp`, regarded as its universal image point.
`isMult_pointOfHom` follows by postcomposition of the identity point.
For affine `Z`, `homEquivMultiplicativePoints` constructs the equivalence

`Hom(D_k(Λ).toGrp, Z.toGrp) ≃ multiplicativePoints Z k Λ`.

Its inverse is the existing `homOfMult`, constructed by specializing a
multiplicative point on every algebra and applying the corepresentation.
The existing universal-point equality `id_comp_homOfMult` gives both inverse
laws; faithfulness of the underlying group-scheme morphism gives the first.
The zero homomorphism corresponds to the identity multiplicative point,
as recorded in `homEquivMultiplicativePoints_zero`.

## Comparison with the actual scheme pullback

Let `K/k` be any field extension and let `Z_K` be the actual commutative
group scheme obtained by pullback along `algebraBaseMap k K`.
`affineBaseChangeEquiv_expMap` applies naturality of
`Lie.affineBaseChangeEquiv` to the group-algebra exponent map. Restricting
that map from `K` to `k` gives the exponent map on the original scheme.
Consequently `isMult_affineBaseChangeEquiv_iff` preserves and reflects
multiplicativity: the point comparison is a group equivalence, so it
preserves the product and reflects equality. Neither result needs `Z`
affine or locally of finite type.

`multiplicativeBaseChangeEquiv` restricts this actual pullback equivalence
to obtain

`multiplicativePoints Z_K K Λ ≃* multiplicativePoints Z K Λ`.

The inverse is the inverse pullback comparison with the reflected
multiplicativity proof. Its group law and inverse laws are inherited from
the ambient affine-point equivalence.

## Purely inseparable descent and vanishing

Assume now that `Z` is affine and its structure morphism is locally of
finite type, that `K/k` is purely inseparable, and that `Λ` is torsion free
(`IsAddTorsionFree Λ`). `homEquivOfIsPurelyInseparable` composes the
universal-point equivalence, the exact coefficient-extension equivalence
`multiplicativePointsEquivOfIsPurelyInseparable`, the inverse pullback
comparison, and the inverse universal-point equivalence. Its result is

`Hom(D_k(Λ).toGrp, Z.toGrp) ≃ Hom(D_K(Λ).toGrp, Z_K.toGrp)`.

Thus its forward construction extends the coefficients of the universal
image point, lifts that point into the actual pullback, and reconstructs
the corresponding homomorphism. The module does not separately identify
this composite with a functorial base change map through a chosen
isomorphism on the source. The explicit composite is sufficient for the
vanishing results below.

`homEquivOfIsPurelyInseparable_zero` proves that the composite preserves
the zero homomorphism, since coefficient extension and the pullback
comparison preserve identity points. Surjectivity then proves
`diagonalizable_hom_eq_zero_of_isPurelyInseparable`: if every homomorphism
from `D_k(Λ)` to `Z` is zero, every homomorphism from `D_K(Λ)` to `Z_K`
is zero.

`gm_hom_eq_zero_of_isPurelyInseparable` specializes this result to actual
cocharacters. It uses the standard isomorphisms from `Gm` to the one-factor
split torus and from that torus to `D(PUnit → ℤ)` over both fields, and
cancels these isomorphisms. Hence vanishing of all actual `Gm ⟶ Z`
homomorphisms survives any purely inseparable extension. The extension
need not be finite or have bounded exponent; the imported exact descent
construction handles each point through its finite coefficient field.

No smoothness, connectedness, perfectness or characteristic restriction
is assumed. These constructions concern commutative targets and do not
prove the general no-torus unipotence statement or maximal-torus base
change. Their provenance is the composition of the imported coordinate
and pullback constructions, rather than an additional structural theorem.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
