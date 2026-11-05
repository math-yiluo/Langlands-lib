# Compatible algebraic extensions and descent of bounds

This derived unit supplies the valued scalar-extension infrastructure for the
spectral boundedness argument. It constructs an actual compatible valuative
relation on an algebraic extension of a nonarchimedean local field and reflects
bounds on all regular functions of actual scalar-extended rational points.
It does not prove `ReductiveSpectralBoundednessStatement`.

## Construction and precise scope

`IsValuativelyCofinal F K` means that every element of `K` is valuatively bounded
above by `algebraMap F K b` for some nonzero `b : F`.
`CofinalValuativeExtension F K` packages a valuative relation on `K`, a
`ValuativeExtension F K` certificate for that relation, and this cofinality
property. The compatibility certificate preserves and reflects comparisons
between images of base-field elements.

`localFieldAlgebraicValuation F K` constructs this package for any actual
nonarchimedean local field `F` and any algebraic field extension `K/F`.
`localFieldAlgebraicClosureValuation F` specializes it to the actual
`AlgebraicClosure F`, with algebraicity discharged internally. Both fields have
arbitrary universe `u`. There is no characteristic, finite-degree, or separability
restriction. The local-field topology and original valuative relation are the
ones provided to the construction.

The implementation first equips `F` with its additive uniformity. Its rank-one
valuation defines a compatible nontrivial norm, and local compactness supplies
completeness. The existing `Langlands.LocalGalois.spectralValuation F K` defines
the extension relation. `spectralNorm_extends` and
`Valued.toNormedField.norm_le_iff` show that it restricts to the original relation
on `F`. For any `c : K`, Mathlib's `NormedField.exists_lt_norm` supplies `b : F`
whose norm is strictly larger than `spectralNorm F K c`. Nonnegativity of the
spectral norm proves `b` is nonzero, and extension of the norm proves the required
comparison. Thus cofinality is proved for this actual construction; it is not
silently assumed for an unrestricted valued extension.

## Actual points and descent

`rationalPointAlgebraHom_geometricRationalPoint` compares evaluation of an actual
`F`-regular function with evaluation of its pullback along the first projection
of `ringBaseChange F K X`. The point is exactly the published
`geometricRationalPoint X p`. The identity says that the latter evaluation is
`algebraMap F K` applied to the former. It needs only an affine scheme `X`, fields
`F` and `K`, and the field algebra structure. Its proof applies faithfulness of
`Spec` to the global-section maps. Naturality of the canonical affine isomorphism
and `geometricRationalPoint_fst` identify the resulting scheme morphisms.

`isAlgebraicallyBounded_of_geometricRationalPoint` explicitly assumes
`ValuativeExtension F K` and `IsValuativelyCofinal F K`. For any subset `S` of the
actual `F`-points, algebraic boundedness of its image in the actual base change
implies `IsAlgebraicallyBounded F X S`. Apply the image bound to the pulled-back
regular function, enlarge the resulting `K`-bound to the image of a nonzero
`F`-element by cofinality, use the evaluation identity, and reflect the comparison
by compatibility. Empty sets are allowed, and no topology or finite-type
hypothesis is needed for this generic lemma.

`isAlgebraicallyBounded_of_localFieldAlgebraicExtension` supplies the compatibility
and cofinality certificates internally using `localFieldAlgebraicValuation`.
Its extension boundedness premise uses exactly the constructed relation on `K`.
It is valid in particular for `K = AlgebraicClosure F`. It retains the boundedness
premise on the actual image; proving that premise remains the representation
argument's responsibility.

## Provenance and corrections

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Definition 2.2.1 and the algebraic-extension convention preceding
Theorem 2.2.9, printed pp.70–71 / PDF pp.101–102, followed by the scalar-extension
argument in Lemma 2.2.11, printed p.72 / PDF p.103. Registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The generic cofinality predicate, certified spectral construction, and actual
scheme-evaluation identity are derived infrastructure, rather than additional
claims attributed to the book.

The November 1, 2024 corrections, Section 2.2, PDF p.24, impose Henselianity
throughout the section and add Henselianity plus separability or discreteness to
Lemma 2.2.5's finite-extension topology comparison. Registered source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The present construction uses the spectral valuation over a complete
nonarchimedean normed field and proves cofinality by unbounded base norms.
It does not invoke Lemma 2.2.5 or assert a finite-dimensional topology comparison.
The generic descent result keeps its compatibility and cofinality hypotheses
explicit. The local-field specialization proves both certificates for its
chosen algebraic extension, including purely inseparable extensions.
