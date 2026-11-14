# An isomorphism criterion for smooth affine schemes over a strictly Henselian DVR

Module `Langlands.GroupScheme.IntegralModel.IntegralPointIsoCriterion`,
namespace `Langlands.GroupScheme.IntegralModel.IntegralPointIsoCriterion`.
All declarations are at an arbitrary universe `u`.

## Statements

Let `R` be a discrete valuation ring which is a Henselian local ring with
separably closed residue field, and let `K` be its fraction field.

- `tensor_mem_range_of_integral_evaluations`: for a smooth `R`-algebra `A`, an
  element `z` of `K ⊗[R] A` whose value under every `R`-algebra point
  `σ : A →ₐ[R] R` (extended `K`-linearly) lies in the image of `R` comes from
  `A` through `a ↦ 1 ⊗ a`. This is the algebra form of Kaletha–Prasad,
  *Bruhat–Tits theory: a new approach* (2023), Lemma 2.10.9, printed p. 123 /
  PDF p. 154 (`kaletha-prasad-2023-bruhat-tits-new-approach`).
- `includeRight_injective`: over any domain `R` with fraction field `K`, the map
  `A → K ⊗[R] A` is injective for a flat `R`-algebra `A` (compare Remark 2.10.3,
  printed p. 122 / PDF p. 153).
- `isIso_of_isIso_baseChange_of_forall_exists_comp_eq`: let `f : X ⟶ Y` be a
  morphism of schemes over `Spec R` with affine `X` and `Y`, `X` flat and `Y`
  smooth over `Spec R`. If the pullback of `f` along `Spec K ⟶ Spec R` is an
  isomorphism and every section `Spec R ⟶ Y` over `Spec R` factors through `f`,
  then `f` is an isomorphism.

## Implemented proof

The integral-evaluation theorem is reused from
`Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof` (the proof of
`smoothHomExtension`). Its declaration is now public, while its two auxiliary
lemmas remain private in that module. A uniformizer divides an element with all point values
divisible by it, because a nonzero element of the reduced smooth special fibre
algebra is nonzero at some rational point (density of points over a separably
closed field) and points lift by Henselian lifting; clearing the denominator of
`z` one uniformizer at a time gives the integral preimage.

For the criterion, write `B → A` for the actual global-section pullback of `f`.
The published coordinate isomorphisms `ringBaseChangeCoordinateAlgEquiv` identify
`K ⊗ B → K ⊗ A` with the global-section pullback of the base-changed morphism,
which is bijective because that morphism is an isomorphism. The identification
is checked on the generators `1 ⊗ b` using the pullback square of the first
projections, and extended to all of `K ⊗ B` by `K`-linearity. Flatness of `A`
and `B` makes `A → K ⊗ A` and `B → K ⊗ B` injective, so `B → A` is injective. For
surjectivity, take `a` in `A` and the preimage `z` of `1 ⊗ a` in `K ⊗ B`. Every
`R`-point of `B` is, by the lifting hypothesis, the composite of an `R`-point of
`A` with `B → A`; so the value of `z` at it is the value of `a`, which is
integral. The first theorem gives `z = 1 ⊗ b`, and injectivity of `A → K ⊗ A`
gives that `b` maps to `a`. A bijective global-section map of affine schemes is an
isomorphism of the schemes, through the canonical isomorphisms with spectra, and
the forgetful functor from schemes over `Spec R` reflects isomorphisms.

The criterion is an internal derived consequence of Lemma 2.10.9 and the
published coordinate-ring infrastructure; it is not a separate numbered result in
the source. It requires no group structure.
