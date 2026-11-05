# Actual apartment pullback through a derived inclusion

Work over a field `k : Type u`, with an actual derived inclusion `d : D → G`,
where `D` is affine and locally of finite type and `G` is affine and smooth.
The supplied split tori `T`, `A`, `S` and morphisms satisfy
`j ≫ d = e ≫ i`. The product of `e : T → S` and `c : A → S` is flat and
surjective as a scheme morphism, and `c ≫ i` is central on every test scheme.
For the apartment construction, `i` and `j` are monomorphic and `i` is an
actual maximal split torus. The scalar valuation is an arbitrary function
`ω : kˣ → ℝ`. These are structural hypotheses of this intermediate
construction; this module does not produce those data.

For every actual `P : KPApartmentData i ω`,
`KPApartmentData.derivedPullback` constructs `KPApartmentData j ω`.
Its carrier is exactly the image of `P.carrier` under the original normalized
derived root-family pullback. Its points are actual pulled-back valuations,
with the original valuation predicate and scalar split-torus compatibility.

The construction proves the following properties:

- The imported `DerivedValuation` theorem
  `IsSplitTorusCompatible.derivedPullback` transfers the original split-torus
  formula with the same `ω`. The proof chooses the corresponding ambient root,
  maps torus conjugation through the actual square, and evaluates its character
  through the original map on torus points.
- The existing complete derived valuation transfer supplies every V0–V5 field
  of the source predicate.
- The carrier is a full orbit under `V T`. An ambient real cocharacter is a
  sum of an image from `V T` and an image from the central complement. The
  central summand fixes normalized families, and the retained summand commutes
  with pullback. Conversely, every source translation is the pullback of the
  corresponding ambient translation.
- The carrier is stable under every actual source normalizer, using
  `DerivedNormalizerMap.normalizerPointsHom` and
  `RootFunctionFamily.derivedPullback_smul`.

`derivedApartmentEquiv` is the literal point pullback
`P.Apartment ≃ (P.derivedPullback ...).Apartment`. Surjectivity comes from the
image carrier, and injectivity uses normalization and the already proved
actual root-point equivalences. Its value formula is definitional.

`derivedApartmentEquiv_vadd` proves, for the original reduced translation
equivalence `E = derivedTranslationEquiv`,

```text
pullback (E(v) +ᵥ x) = v +ᵥ pullback x.
```

`derivedApartmentEquiv_smul` proves the same compatibility for the original
normalizer actions, with a source normalizer mapped to its actual ambient
point image. `derivedApartmentAffineEquiv` bundles the point bijection as an
affine equivalence whose derivative is `E.symm`. Its value formula again
preserves the literal family pullback.
`derivedApartmentAffineEquiv_normalizer` expresses the original normalizer
intertwining as equality of the two composite affine equivalences.

This is internal content built from the actual derived-root, valuation,
translation and action comparisons. Its bundling follows
`CentralIsogenyApartment`, replacing surjectivity of the full torus
cocharacter map by the retained/central decomposition on the reduced space.
There is no new external theorem invoked here.

`KPApartmentData` includes split-torus compatibility, not full compatibility
with every element of the algebraic centralizer. This module constructs no
source `CentralizerDatum`, proves no full-centralizer V6 or source apartment
axioms, and does not establish the final simply connected normalizer image
equality.
