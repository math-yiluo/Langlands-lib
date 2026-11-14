# Generic fibres and canonical restriction of integral models

This is a derived construction used in the root-model restriction step of
Kaletha–Prasad, Proposition C.5.1 (printed pp.703–704 / PDF pp.734–735).
It makes the generic identification and its compatibility with model maps
explicit. It does not assert the full root-depth kernel theorem.

Let `A` and `O` be commutative domains with fraction fields `F` and `K`,
respectively. Suppose `O` is a finite projective `A`-algebra and the given
`A`-algebra structures on `K`, through `O` and through `F`, agree. All four
rings are in an arbitrary common universe `u`. The generic groups `G`
and `H` are affine group schemes locally of finite type over `K`.

`coefficientFaithful` proves that `A` acts faithfully on `O`: the composite
`A → O → K` is the composite of the two injective maps `A → F → K`.
Finiteness makes `O` algebraic over `A`, so Mathlib's fraction-ring
localization and pushout results apply. `genericFinite` derives that `K`
is finite over `F`. No separate finiteness, faithfulness or coefficient
pushout premise is supplied.

For every commutative `F`-algebra `R`, `coefficientEquiv` is the actual
`O`-algebra equivalence

`O ⊗[A] R ≃ₐ[O] K ⊗[F] R`.

It sends `o ⊗ r` to the image of `o` in `K` tensored with `r`.
`coefficientEquiv_naturality` proves compatibility with every `F`-algebra
map. The construction uses `Algebra.IsPushout.cancelBaseChangeAlg`, with
the fraction-ring pushout derived by the instances in
`Mathlib.RingTheory.Algebraic.Integral`.

For an actual `IntegralModel O K G` named `M`,
`genericTensorPointsEquiv` first extends coefficients using this
equivalence, applies the actual multiplicative base-change point
comparison for `M.group`, and finally uses `M.genericIso`. Naturality in
`R` is proved by the coefficient square, naturality of the base-change
point comparison, and associativity with the generic identification.

`genericGroup A F O K G` is the actual affine restriction
`AffineWeil.groupScheme F K G`; its abbreviation installs the derived
finite-dimensionality instance. `pointEquiv` composes the actual
base-change tensor-point comparison for restriction from `O` to `A`, the
preceding generic comparison, and the inverse restriction point
comparison for `G`. It is natural in all affine `F`-algebras.
`affinePointIso` packages these multiplicative equivalences as a natural
isomorphism, and `iso` reconstructs an actual group-scheme isomorphism

`(Res_{O/A} M.group)_F ≅ Res_{K/F} G`.

The reconstruction uses `AffinePointComparison.iso`; `iso_hom_points`
records its exact action on every affine test algebra.

If `φ : M.Hom N f` is an original compatible model homomorphism,
`genericTensorPointsEquiv_target` proves compatibility on tensor-valued
points. The proof uses the actual pullback projection for base change
and then `φ.generic_comm`. Combining this with naturality of the two
restriction point comparisons proves `pointEquiv_target`. Affine tests
then establish `iso_naturality`: the base-changed restricted map followed
by the target generic identification equals the source identification
followed by the actual restriction of `f`. This square is proved from the
original compatible homomorphism; it is not a new input.

When `M.group` is smooth, `model` is `IntegralModel.affineWeil` with this
canonical generic isomorphism. Its integral group is the actual
`AffineWeil.groupScheme A O M.group`, and `model_isSmooth` inherits the
published smoothness of restriction. For smooth `M` and `N`, `modelHom`
restricts `φ.hom` and uses the proved generic square. `model_hom_eq`
uses generic rigidity to identify every compatible extension with that
same restricted map. If `A` is local, `model_specialFibreMap_eq` identifies
its actual residue-field map with the actual residue-field base change
of `AffineWeil.map A O φ.hom`.

The general coefficient construction is derived from existing tensor,
localization and affine-point APIs. The source motivation is KP C.5.1,
where root models are formed by restriction from coefficient integer
rings. Identifying root filtrations with these models, proving comparison
with arbitrary supplied root presentations, and assembling all root
cases of C.5.3 remain separate obligations. No host Proposition 8.4.15
kernel theorem is used.
