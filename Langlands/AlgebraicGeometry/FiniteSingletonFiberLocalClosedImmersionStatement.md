# Finite stalks and closed-immersion neighborhoods at a singleton finite fiber

This internally derived supporting statement concerns an actual finite scheme
morphism `f : X ⟶ Y`, with both schemes in any common universe, and a point
`x : X`. The sole fiber hypothesis says that the entire inverse image of the
underlying point `f x` is the singleton `{x}`. It concerns the topological fiber,
without asserting that its scheme structure is reduced.

The conclusion contains two related assertions:

- The actual contravariant map of structure-sheaf stalks
  `(f.stalkMap x).hom : O_(Y,f x) →+* O_(X,x)` is finite. Here `RingHom.Finite`
  means that its codomain is a finitely generated module over its domain with
  the scalar action induced by this specific ring homomorphism.
- If this same stalk map is surjective, there is an open neighborhood `V` of
  `f x` in `Y` such that the restriction `f ∣_ V` is a closed immersion. Its
  source is the entire inverse image of `V`, rather than a chosen neighborhood
  of `x` within that inverse image.

The finite-stalk conclusion uses the singleton hypothesis: arbitrary stalk
maps of finite scheme morphisms need not themselves be finite. The second
conclusion spreads surjectivity; it does not claim an isomorphism or injectivity
of the stalk map. No field, rational-point, Noetherian, reducedness,
separatedness, unramifiedness, stalk-injectivity, or tangent hypothesis is imposed. Empty schemes are allowed in
the universal statement; specifying `x` makes that particular source nonempty.

The formulation is derived from the pinned Mathlib interfaces. On affine
neighborhoods, `IsAffineOpen.arrowStalkMapIso` identifies the actual stalk map
with a map of localized rings. A singleton fiber identifies the primes above
the corresponding base prime. `Localization.finite_of_primesOver_eq_singleton`
gives finite generation after these localizations, with no unramifiedness
hypothesis. Finite generation then lets surjectivity spread after inverting one
base element: choose preimages of finitely many algebra generators and clear
their denominators. The existing proof of
`Localization.exists_awayMap_bijective_of_localRingHom_bijective` contains this
surjectivity argument; only its surjectivity part is relevant here. The affine
surjective-ring-map criterion then gives the indicated closed immersion.
These APIs explain the internal provenance and intended use, rather than
providing a proof in this module. This module defines a proposition only.

The combined geometric formulation and this statement draft were prepared by
Worker 487. It is an internal derived proposition, rather than a quotation of
a theorem in the sources below. In particular, the bijectivity result cited
for its denominator argument is stronger in a different direction: its
injectivity and finitely generated kernel assumptions are not hypotheses here.
No projectivity criterion, ample line bundle, cotangent comparison or
residue-field-to-stalk surjectivity result is asserted or assumed.

The original source locators are in pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

| Registered source | File and precise locator | Role |
| --- | --- | --- |
| `mathlib-ag-finite-5ed296525643` | `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, lines 36–43 (`IsFinite`, `Scheme.Hom.finite_app`) | Finite maps have affine whole inverse images of affine target opens and finite section maps. |
| `mathlib-ag-affinescheme-5ed296525643` | `Mathlib/AlgebraicGeometry/AffineScheme.lean`, lines 880–911 (`IsAffineOpen.arrowStalkMapIso`) | Identifies the actual stalk map with the induced local ring map. |
| `mathlib-unique-prime-localring-5ed296525643` | `Mathlib/RingTheory/Unramified/LocalRing.lean`, lines 158–196 (`Localization.finite_of_primesOver_eq_singleton`) and 253–291 (`Localization.exists_awayMap_bijective_of_localRingHom_bijective`) | Singleton-prime localization finiteness and the surjectivity-only denominator-clearing route. |
| `mathlib-ag-closedimmersion-5ed296525643` | `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`, lines 116–122 (`IsClosedImmersion.of_surjective_of_isAffine`) | A surjective section map between affine schemes induces a closed immersion. |
