# Finite normalization pieces of affine morphisms

Author: Worker 185.

This is a helper module for the proof `Langlands.AlgebraicGeometry.LangWeil.finiteNormalizationCover`
of `Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement`. Its declarations
are in the namespace `Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction`. It
proves the affine case: for a finite-type algebra `A` over a Noetherian ring `R`, finitely many
pieces (structure `Piece` of `FiniteNormalizationCoverPieces`) of
`Spec.map (algebraMap R A) : Spec A ⟶ Spec R` cover every field-valued point of `Spec A`.

Provenance: internal. The route stratifies the source ring `A` by its primes and applies generic
Noether normalization to each quotient `A ⧸ Q` over `R ⧸ (Q ∩ R)`. This differs from the route
sketched in the statement's Markdown, which stratifies the base. Throughout, a morphism
`x : Spec K ⟶ Spec A` corresponds to the ring map `Spec.preimage x : A → K`.

## A piece from a finite injective polynomial map

`exists_piece_of_finite_injective` has the following setup:

- surjective ring maps `πR : R → D` and `πA : A → C`, compatible with the algebra maps
  `R → A` and `D → C`;
- an element `r : D`, a localization `D'` of `D` away from `r`, and a localization `C'` of `C`
  at the image of the powers of `r`, with compatible algebra structures;
- a finite injective `D'`-algebra map `ψ : D'[X] →ₐ[D'] C'` with variables `ULift (Fin d)`;
- an element `g : A` with `πA g` equal to the image of `r` in `C`.

It constructs a piece of `Spec A ⟶ Spec R` through which every `x : Spec K ⟶ Spec A` factors
whenever the kernel of `A → K` contains `ker πA` and `g` does not map to `0` in `K`. The piece is:

- `base = Spec D'`, an affine scheme, with `baseMap` the composite of the open immersion
  `Spec D' ⟶ Spec D` (`IsOpenImmersion.of_isLocalization`) and the closed immersion
  `Spec D ⟶ Spec R` (`IsClosedImmersion.spec_of_surjective`);
- `source = Spec C'`, with `sourceMap` the composite `Spec C' ⟶ Spec C ⟶ Spec A`, also an open
  immersion followed by a closed immersion. `C'` is a localization of `C` away from the image of
  `r`;
- `dimension = d`, and `normalization` is `Spec.map ψ` followed by the inverse of Mathlib's
  isomorphism `AffineSpace.SpecIso` between `Spec D'[X]` and the relative affine space over
  `Spec D'`. It is finite because `ψ` is finite (`IsFinite.SpecMap_iff`). It is surjective
  because `ψ` is integral and injective, so every prime of `D'[X]` is a contraction
  (`RingHom.IsIntegral.comap_surjective`).
- By `AffineSpace.SpecIso_inv_over`, `normalization` followed by the projection to `Spec D'` is
  `Spec.map (algebraMap D' C')`. Then `comm` reduces to an identity of ring maps that follows
  from the scalar towers and the compatibility of `πR` and `πA`.
- `fibreChain`: for a point `t` of `Spec D'`, `exists_ltSeries_fibre` gives a strictly
  increasing series of length `d` of primes of `C'`, all lying over `t`. In a prime spectrum,
  `P ≤ P'` means that `P` specializes to `P'` (`PrimeSpectrum.le_iff_specializes`), and a strict
  inequality gives distinct points.

Covering: let `x : Spec K ⟶ Spec A` with `χ₀ : A → K` its ring map. If `ker πA ≤ ker χ₀`,
then `χ₀` factors as `χ ∘ πA` (`RingHom.liftOfSurjective`). If moreover `χ₀ g ≠ 0`, then `χ`
sends the image of `r` to `χ₀ g`, a unit, so `χ` extends to `ℓ : C' → K`
(`IsLocalization.lift`). The morphism `Spec.map ℓ : Spec K ⟶ Spec C'` composed with `sourceMap`
is `x`, by `Spec.map_preimage` and functoriality of `Spec.map`.

## A piece for each prime

`exists_piece`: let `A` be a finite-type `R`-algebra and `Q` a prime of `A`. Then there are
`g ∉ Q` and a piece covering every field-valued point of `Spec A` whose kernel contains `Q` and
does not contain `g`. Set `D = R ⧸ (Q ∩ R)` and `C = A ⧸ Q`. These are domains, `D → C` is
injective, and `C` is of finite type over `D`. `exists_away_finite_injective` gives `r ≠ 0` in
`D` and a finite injective `ψ`. Write `r` as the class of some `r₀ : R` and take `g` to be the
image of `r₀` in `A`. Then `g ∉ Q` because `r ≠ 0`. Apply `exists_piece_of_finite_injective`
with the quotient maps, whose kernel in `A` is `Q` (`Ideal.mk_ker`).

## Finitely many pieces

`exists_finite_affine_pieces`: for `R` Noetherian and `A` of finite type over `R`, there is a
finite set of pieces of `Spec A ⟶ Spec R` such that every `x : Spec K ⟶ Spec A`, for a field `K`
in universe `u`, factors through `sourceMap` of one of them. `A` is Noetherian
(`Algebra.FiniteType.isNoetherianRing`). Apply `exists_finite_cover_of_prime` to the relation "the
piece covers every field-valued point whose kernel is `P`", with the hypothesis supplied by
`exists_piece`. The kernel of `A → K` is prime, so every field-valued point is covered.
