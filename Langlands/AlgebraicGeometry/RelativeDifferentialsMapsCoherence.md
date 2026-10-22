# Coherence of relative differential maps

`Langlands.Scheme.relativeDifferentialsMapLaws` proves exactly
`RelativeDifferentialsMapLawsStatement.{u}` from
`RelativeDifferentialsMapsStatement`. The proof is uniform in the scheme
universe and assumes only the commuting triangles in that statement. It
concerns the actual sheaves `relativeDifferentials` and the actual maps
`relativeDifferentialsMap`; no universality, smoothness, flatness or
affineness hypothesis is assumed.

## Characterization

The first clause is an equivalence. If the adjoint of `α`, postcomposed
with the distinguished derivation, is the precomposed derivation, then
`relativeDifferentialsMap_unique` gives `α = relativeDifferentialsMap g w`.
Conversely, after substituting `α`, the condition is the factorization
lemma `relativeDifferentialsMap_fac`.

## Pushforward identity and composition

The proof first establishes two formulas for the adjoint pushforward maps
`relativeDifferentialsPushforwardMap`. In both, `relativeDifferentials_hom_ext`
reduces an equality of morphisms out of the differential sheaf to equality
after postcomposition with its universal derivation.

- `relativeDifferentialsPushforwardMap_id`: the map for `𝟙 X`, followed by
  the component of `pushforwardId X` in its forward direction, is the
  identity. This uses `RelativeDerivation.postcomp_comp`, the factorization
  lemma `relativeDifferentialsPushforwardMap_fac`,
  `RelativeDerivation.precompOver_id` and `RelativeDerivation.postcomp_id`.
- `relativeDifferentialsPushforwardMap_comp`: the map for `h`, followed by
  the pushforward along `h` of the map for `g` and the component of
  `pushforwardComp g h` in its forward direction, is the map for `g ≫ h`.
  This rewrites with `RelativeDerivation.postcomp_comp`, the factorization
  lemma three times, target naturality of precomposition
  `RelativeDerivation.precompOver_postcomp`, and
  `RelativeDerivation.precompOver_comp`.

## Transport to pullback maps

Three private lemmas compute the hom equivalence of Mathlib's
`pullbackPushforwardAdjunction` on the pullback coherence maps.

- `homEquiv_conjugate` is a general fact about adjunctions `L₁ ⊣ R₁` and
  `L₂ ⊣ R₂` with a natural transformation `α : L₂ ⟶ L₁`: the second hom
  equivalence of `α.app A ≫ f` is the first hom equivalence of `f` followed
  by the component of the conjugate transformation. It expands the hom
  equivalence by the adjunction unit, applies `unit_conjugateEquiv`, and
  then naturality of the conjugate.
- `pullbackHomEquiv_id` states that the adjoint of the component of
  `(pullbackId X).hom` is the component of `(pushforwardId X).inv`. It
  applies `unit_conjugateEquiv` directly to the identity adjunction and the
  adjunction for `𝟙 X`, then Mathlib's `conjugateEquiv_pullbackId_hom`.
- `pullbackHomEquiv_comp` computes the adjoint along `g ≫ h` of
  `(pullbackComp g h).inv.app A ≫ (pullback g).map α ≫ β`. It applies
  `homEquiv_conjugate` to the composite adjunction and the adjunction for
  `g ≫ h`, rewrites with Mathlib's `conjugateEquiv_pullbackComp_inv` and
  `Adjunction.comp_homEquiv`, and finishes with naturality of the hom
  equivalences in both arguments.

Injectivity of the hom equivalence then gives the pullback laws.

- `relativeDifferentialsMap_id`: by `relativeDifferentialsMap_adjoint` and
  `pullbackHomEquiv_id`, it suffices to compare with the component of
  `(pushforwardId X).inv`. Composing with the monomorphism given by the
  component of `(pushforwardId X).hom` reduces this to
  `relativeDifferentialsPushforwardMap_id`.
- `relativeDifferentialsMap_comp`: `pullbackHomEquiv_comp` and three uses of
  `relativeDifferentialsMap_adjoint` turn both sides into pushforward maps,
  and `relativeDifferentialsPushforwardMap_comp` identifies them.

These lemmas use the exact pullback coherence isomorphisms of the target
statement: the forward direction of `Modules.pullbackId` and the inverse
direction of `Modules.pullbackComp g h`.

## Packaging and provenance

`relativeDifferentialsMapLaws` combines the characterization with
`relativeDifferentialsMap_id` and `relativeDifferentialsMap_comp`. These are
the properties of Stacks Project Lemmas 17.28.12 and 17.28.13 (tags 08RU and
01UW), proved here for the sheaves constructed in this Library. The source
omits the proofs. This module uses the adjunction argument described above.
Registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
file `08RL.html`.

The public lemmas `relativeDifferentialsPushforwardMap_id`,
`relativeDifferentialsMap_id` (a `simp` lemma),
`relativeDifferentialsPushforwardMap_comp` and
`relativeDifferentialsMap_comp` are available to downstream modules.
