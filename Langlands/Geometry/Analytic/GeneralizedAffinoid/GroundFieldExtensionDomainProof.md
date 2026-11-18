# Ground field extension preserves affinoid domains

This module proves the Library statement
`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.DomainPreservationStatement`
(module `GroundFieldExtensionDomainStatement`) as the theorem

`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.domainPreservation : DomainPreservationStatement.{u, v}`.

Let `K` and `L` be complete ultrametric normed fields with
`NormedAlgebra K L`, in independent universes `u` and `v`. If a bounded map
`i : A → B` of presented `K`-affinoid algebras represents a closed subset `V` of the
spectrum of `A` (`Represents K i V`), then the ground-field-extended map
`map K L i : A_L → B_L` represents the preimage
`spectrumProjection K L A ⁻¹' V` against every presented `L`-affinoid test
algebra. The theorem allows arbitrary field extensions and positive radii,
including trivially valued fields, nonreduced or zero algebras, and empty
spectra. Its axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`.

All declarations below live in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension`. The proof
uses the helper module `GroundFieldExtensionRationalChart` (ground field
extension of rational charts), which is documented in its own Markdown file.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Definition 2.2.1 (printed p. 27) gives the universal property of an
affinoid domain. The proof of Proposition 2.2.4 (printed p. 29) uses base
change of affinoid domains for an extension over which the algebras are
strictly affinoid. The proof of Proposition 2.2.3(i) (printed p. 28) uses a
Gerritzen–Grauert cover in the strict case. The Lean proof uses the Library's
`Domain.finiteRationalCover` for arbitrary positive radii and trivial or
nontrivial valuations, together with
`Domain.FiniteCover.represents_of_finiteCover`. The comparisons of chart
algebras and the finite-cover recognition argument below are internal to
the Library's presentations.
Registered source `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.

## Small general lemmas

- `comap_comp` identifies the spectrum map of `g.comp f` pointwise with the
  composite of the spectrum maps in reverse order.
- `comap_injective_of_represents` applies `Domain.spectrumMap_injective` to
  the domain defined by a representing map.
- `represents_range` rewrites the represented set of `g` as the range of its
  spectrum map.
- `mapEquiv K L e` shows that the ground field extension of a bounded `K`-algebra
  equivalence `e : A ≃ B` is a bounded `L`-algebra equivalence `A_L ≃ B_L`,
  with forward map `map K L e` and inverse `map K L e.symm`. The inverse laws
  follow from `map_comp` and `map_id`. `mapEquiv_toBoundedAlgHom` records its
  underlying map.

## Rational charts lying over a domain

In this section `i : A → B` represents `V`, `D` is a rational chart of `A`, and
`α : B → D.algebra` satisfies `α ∘ i = D.baseMap`. Write
`P = RationalChart.pullback i D`, the Library's coefficient pullback of `D`
along `i`, a rational chart of `B` whose locus is the preimage of `D.locus`
(`RationalChart.pullback_locus`), with comparison map
`RationalChart.pullbackMap i D : D.algebra → P.algebra` satisfying
`pullbackMap ∘ D.baseMap = P.baseMap ∘ i`.

- `hasImageIn_pullback` identifies where the spectrum map of `α` lands.
  The spectrum map of `α ∘ i = D.baseMap` takes every point of
  `D.algebra` into `D.locus`, so the spectrum map of `α` takes every point of
  `D.algebra` into `P.locus`.
- `pullbackInverse D α hα : P.algebra → D.algebra` is the factorization of `α`
  through `P.baseMap`, given by the universal property of `P`.
  `pullbackInverse_comp_baseMap` states
  `pullbackInverse ∘ P.baseMap = α`.
- `pullbackInverse_comp_pullbackMap` proves `pullbackInverse ∘ pullbackMap = id`
  by uniqueness for `D`, since both sides agree after
  composing with `D.baseMap` (both give `α ∘ i = D.baseMap`).
- `pullbackMap_comp_arrow` proves `pullbackMap ∘ α = P.baseMap` by uniqueness in
  the universal property of `i` (the hypothesis `Represents K i V`), since
  both sides agree after composing with `i`.
- `pullbackMap_comp_pullbackInverse` proves `pullbackMap ∘ pullbackInverse = id` by
  uniqueness in the universal property of `P`, using the two previous facts.
- `pullbackEquiv hV D α hα : D.algebra ≃ P.algebra` is the resulting bounded
  `K`-algebra equivalence, with forward map `pullbackMap`.
- `pullback_baseMap_comp` records `P.baseMap ∘ i = pullbackEquiv ∘ D.baseMap`.

## Extension to `L`

Now `L` is complete as well.

- `represents_local` shows that for `D`, `α` and `P` as above, the composite
  `map K L P.baseMap ∘ map K L i` represents the range of its spectrum map.
  The helper lemma `represents_map_baseMap K L D` says that
  `map K L D.baseMap` represents `spectrumProjection K L A ⁻¹' D.locus`.
  Post-composing with the equivalence `mapEquiv K L (pullbackEquiv ..)`
  (Library `Represents.postcomp_equiv`) and rewriting with `map_comp` and
  `pullback_baseMap_comp` turns this map into
  `map K L P.baseMap ∘ map K L i`. Then `represents_range` applies.

For the rest of the section, `D : Fin n → RationalChart K A` is a finite family
of rational charts covering `V` (`hcov : ∀ x ∈ V, ∃ k, x ∈ (D k).locus`), with
arrows `α k : B → (D k).algebra` such that `α k ∘ i = (D k).baseMap`.

- `mem_pullback_locus_iff` gives the membership test for a point `y` of the
  spectrum of `B_L`.
  `spectrumProjection K L B y` lies in the locus of the pulled-back chart
  `RationalChart.pullback i (D k)` if and only if the image of `y` in the
  spectrum of `A` (through the spectrum map of `map K L i` and
  `spectrumProjection K L A`) lies in `(D k).locus`. This is
  `pullback_locus` together with `spectrumProjection_naturality`.
- `extendedCover K L hV D hcov : Domain.FiniteCover (Domain.whole L B_L)`. Its
  `k`-th member is the domain of `B_L` with algebra
  `algebra K L (pullback i (D k)).algebra`, structure map
  `map K L (pullback i (D k)).baseMap` and locus the preimage under
  `spectrumProjection K L B` of the pulled-back locus, represented by
  `represents_map_baseMap` for the chart `pullback i (D k)` of `B`. For every
  point of the spectrum of `B_L`, naturality and the image condition put its
  image in the spectrum of `A` in `V`. The image thus lies in some
  `(D k).locus`, and `mem_pullback_locus_iff` puts the original point in the
  corresponding cover member.
- `comap_map_injective` proves injectivity of the spectrum map of `map K L i`. If two
  points `y₁`, `y₂` have the same image, choose `k` with the common image over
  `(D k).locus`. Both points then lie in the range of the spectrum map of
  `map K L (pullback i (D k)).baseMap`, say as images of `w₁`, `w₂`. The images
  of `w₁` and `w₂` under the spectrum map of the composite
  `map K L P.baseMap ∘ map K L i` coincide, and this spectrum map is injective
  by `represents_local` and `comap_injective_of_represents`. Hence `w₁ = w₂`
  and `y₁ = y₂`.
- `range_comap_map` identifies the range of the spectrum map of `map K L i` with
  `spectrumProjection K L A ⁻¹' V`. The inclusion `⊆` is naturality plus the
  image condition of `Represents K i V`. For `⊇`, a point `z` over `V` lies
  over some `(D k).locus`, hence (by `represents_map_baseMap K L (D k)`) is the
  image of some `w` under the spectrum map of `map K L (D k).baseMap`. By
  `map_comp` and `hα k`,
  `map K L (D k).baseMap = map K L (α k) ∘ map K L i`, so
  `z` is the image of the point `w` pulled back along `map K L (α k)`.
- `represents_of_rationalCover` proves `Represents L (map K L i)
  (spectrumProjection K L A ⁻¹' V)`. The Library criterion
  `Domain.FiniteCover.represents_of_finiteCover`, applied to the cover
  `extendedCover`, the injectivity `comap_map_injective` and the local
  representations `represents_local`, gives the representation of the range
  of the spectrum map of `map K L i`. `range_comap_map` identifies this range.

## The theorem

The proof of `domainPreservation` applies `Domain.finiteRationalCover` to the
domain `⟨B, i, V, hV⟩`. This gives finitely many rational charts `D k` of `A` covering `V`
together with domain morphisms `(D k).toDomain ⟶ ⟨B, i, V, hV⟩`, whose
`restriction` fields are arrows `α k : B → (D k).algebra` with
`α k ∘ i = (D k).baseMap` (`comp_baseMap`). Then
`represents_of_rationalCover` gives the claim.
