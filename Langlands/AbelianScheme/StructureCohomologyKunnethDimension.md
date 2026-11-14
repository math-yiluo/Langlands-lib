# Dimensions of structure-sheaf cohomology of a product over a field

Module `Langlands.AbelianScheme.StructureCohomologyKunnethDimension`, namespace
`Langlands.AbelianScheme`.

## Purpose

`FieldH2ExteriorCoproductComparisonStatement` asks for a linear equivalence
`κ : H²(A ⨯ A, 𝒪) ≃ H²(A) × ⨂² H¹(A) × H²(A)`. The intended `κ` is the inverse
of an explicit map `Φ` in the other direction. This module supplies the
surjectivity half of that construction by a dimension count: once `Φ` is
injective, it is bijective. The injectivity of `Φ` is a separate step.

## Definitions and results

Throughout, `K` is a field, `X` and `Y` are objects of `Over (Spec K)`, and
`structureCohomology X n := (relativeCohomology X.hom n).obj (SheafOfModules.unit X.left.ringCatSheaf)`
(an `abbrev`). This is exactly the `Hⁿ` of the target statement.

- `finiteDimensional_structureCohomology` (instance): `Hⁿ(X, 𝒪)` is
  finite-dimensional if `X.hom` is proper. This is the Library's
  `properCoherentCohomologyFinite`, applied to the quasi-coherent structure sheaf
  (`CechDegreeOne.isQuasicoherent_unit`), whose sections are finite over the
  sections ring (`Module.Finite.self`).
- `bijective_structureRingHom`: if `X.hom` is smooth, proper and geometrically
  connected, then `structureRingHom X.hom : K ⟶ Γ(X, ⊤)` is bijective. It is an
  isomorphism, since the Library's `smoothProperConnectedGlobalFunctions` makes
  `X.hom.appTop` an isomorphism.
- `finrank_structureCohomology_zero`: under the same hypotheses,
  `dim H⁰(X, 𝒪) = 1`. The Library's `relativeCohomologyZeroIso` identifies
  `H⁰(X, 𝒪)` with the `K`-module global sections. The map `r ↦ r • 1` from `K`
  is `structureRingHom`, hence a linear bijection.
- `antidiagonalEquiv n : Fin (n + 1) ≃ {ab : ℕ × ℕ // ab.1 + ab.2 = n}` sends
  `i` to `(i, n - i)`. It also gives the `Fintype` instance on the index set.
- `externalTensorUnitIso X Y` is the isomorphism
  `tensorObj (p₁^* 𝒪_X) (p₂^* 𝒪_Y) ≅ 𝒪_{X ⨯ Y}`, built from the Library's
  `pullbackUnitIso` on both factors and then `tensorLeftUnitor`.
- `finrank_structureCohomology_prod`: for `X`, `Y` smooth and proper,
  `dim Hⁿ(X ⨯ Y, 𝒪) = ∑_{(a, b), a + b = n} dim Hᵃ(X, 𝒪) · dim Hᵇ(Y, 𝒪)`. Apply the
  published `coherentFieldExternalTensorKunneth` to the trivial line bundles
  (`LineBundle.trivial`, whose underlying sheaf is the structure sheaf). Change
  the coefficient with `externalTensorUnitIso`. Then use
  `Module.finrank_directSum` and `Module.finrank_tensorProduct`.
- `tensorPowerTwoBasis H` (from `Basis.piTensorProduct`),
  `finiteDimensional_tensorPower_two`, and `finrank_tensorPower_two`:
  `dim ⨂[K]^2 H = dim H · dim H` for a finite-dimensional `H`.
- For `A : AbelianScheme (Spec K)`, `isProper_prod_hom` says `(A.X ⨯ A.X).hom`
  is proper: it is the composite of the base change `prod.snd.left` of
  `A.X.hom` with `A.X.hom`.
- `finrank_structureCohomology_prod_two`:
  `dim H²(A ⨯ A, 𝒪) = dim H²(A, 𝒪) + dim H¹(A, 𝒪) · dim H¹(A, 𝒪) + dim H²(A, 𝒪)`.
  This is the case `n = 2` of `finrank_structureCohomology_prod`, with
  `dim H⁰(A, 𝒪) = 1`.
- `bijective_of_injective_degreeTwo A Φ hΦ`: every injective `K`-linear map
  `Φ : H²(A) × ⨂[K]^2 H¹(A) × H²(A) ⟶ H²(A ⨯ A, 𝒪)` is bijective. The domain
  and codomain have equal finite dimension (`Module.finrank_prod`,
  `finrank_tensorPower_two`, `finrank_structureCohomology_prod_two`), so we can
  apply `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.
  `degreeTwoEquivOfInjective` packages `Φ` as a linear equivalence.

## Scope and exclusions

This module proves no injectivity statement for any particular `Φ`. It uses
only the published Library theorems named above (Künneth, finiteness, global
functions). None of them is one of the representability and dual-scheme
statements excluded by Task 6105, or a proof of
`FieldH2PrimitiveInjectivityStatement`.

## Provenance

This is internal infrastructure: linear algebra combined with the published
coherent Künneth formula (`CoherentFieldExternalTensorKunnethStatement`, whose
proof is in the Library). The dimension identity is the degree-two case of the
Künneth formula for the structure sheaf, as used in the registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.14)–(6.17).

The abbreviation `structureCohomology` is reused from
`Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology` in
[ElementaryArtinianIdealCohomologyNaturalityStatement](../AlgebraicGeometry/Picard/ElementaryArtinianIdealCohomologyNaturalityStatement.md).
