# Proof: naturality of the analytic points of algebraic rational points

Lean module: `Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityProof`.

Main theorem: `Langlands.Analytic.AffineAnalytification.affineAnalytificationRationalPointNaturality`,
of type `AffineAnalytificationRationalPointNaturalityStatement.{u, v, w}`.

The target statement is
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationRationalPointNaturalityStatement`
(module `Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityStatement`).
For a complete nonarchimedean nontrivially normed field `K`, finite polynomial
presentations `P` of `A` and `Q` of `B`, a `K`-algebra map `f : A →ₐ[K] B` and an
algebraic point `φ : AlgPoint K B K`, it asserts

```
baseMap K P Q f (analyticPoint K Q φ) = analyticPoint K P (AlgPoint.precomp f φ).
```

This proof adapts the complete public draft shared by Worker 3519 for Task 7072,
revision 1. Its Lean proof is unchanged from that draft.

The proof imports only the statement module, which in turn imports the published
`AffineAnalytificationRationalPoints` and `AffineAnalytificationMap`. It uses no
other axioms than `propext`, `Classical.choice` and `Quot.sound`.

## Implemented route

All work happens in one bounded chart. Fix `k` with `hk : RadiusAdmits K Q φ k`.

1. `character_generatorValue`. The evaluation character `character K Q hk` of `φ`
   on the `k`-th chart algebra of `Q` sends the lifted generator value
   `generatorValue K P Q f k t` to the `t`-th coordinate of `φ ∘ f` for the
   presentation `P`. The proof rewrites the generator value as the image of
   `f (P.map (X t))` under the coordinate-algebra map
   (`generatorValue_eq_algebraMap`), then applies `character_algebraMap`; the
   result is `φ (f (P.map (X t)))`, which is `pointCoordinates K P (φ ∘ f) t` by
   definition.

2. `radiusAdmits_precomp`. If `φ` lies in the `k`-th polydisc of `Q`, then
   `φ ∘ f` lies in the `level K P Q f k`-th polydisc of `P`. For each coordinate
   `t`, step 1 writes the coordinate as the character value at the generator
   value. The spectrum point of the character is bounded by the norm of the chart
   algebra (`BanachSpectrum.le_norm` applied to `spectrumPoint K Q hk`), and the
   generator value has norm at most `radius K (level K P Q f k)`
   (`norm_generatorValue_le`).

3. `character_comp_chartMap`. The character of `φ` composed with the chart map
   `chartMap K P Q f k` equals the character of `φ ∘ f` at the admissible level
   from step 2. Both sides are bounded `K`-algebra maps out of the presented
   affinoid chart algebra of `P`, so by `PresentedAffinoidAlgebra.hom_ext_coordinate`
   it is enough to compare them on the coordinates. The chart map sends the
   `t`-th coordinate to the generator value (`chartMap_coordinate`), step 1
   evaluates that, and `character_coordinate` gives the same value on the other
   side.

4. `comap_chartMap_spectrumPoint`. Pulling the spectrum point of `φ` back along the
   chart map gives the spectrum point of `φ ∘ f`. By `BanachSpectrum.ext` both are
   compared at each element `a`; both values are norms of character values, and
   step 3 identifies the characters.

5. Main theorem. Take `k = minimalRadius K Q φ` with
   `radiusAdmits_minimalRadius`. Unfolding `analyticPoint` on the left, the
   defining equation `baseMap_chart` of the analytification map turns
   `baseMap K P Q f (chart K Q k (spectrumPoint K Q hk))` into the chart point of
   level `level K P Q f k` of the pulled-back spectrum point. Step 4 rewrites it to
   `chart K P (level K P Q f k) (spectrumPoint K P _)`, and
   `chart_spectrumPoint` (every admissible chart computes the same analytic point)
   identifies it with `analyticPoint K P (AlgPoint.precomp f φ)`.

## Mathematical content

This is the affine case of the compatibility of the identification
`X(K) = X^an(K)` with morphisms (Conrad–Temkin 2009, Example 2.3.2 and
Theorem 2.2.3, as used in Conrad 2011, printed p.19). In the Lean route the
compatibility is a direct computation: on a bounded chart the analytic point of
`φ` is the multiplicative seminorm `a ↦ |χ_φ(a)|` of the evaluation character, the
analytification map is pullback along the chart map, and the evaluation character
of `φ` composed with the chart map is the evaluation character of `φ ∘ f` because
both agree on the coordinates.

The auxiliary lemmas `character_generatorValue`, `radiusAdmits_precomp`,
`character_comp_chartMap` and `comap_chartMap_spectrumPoint` are internal steps of
this proof; they are stated for an arbitrary admissible level `k`, not only the
minimal one.

## Sources and scope

The contextual sources, already registered in the project literature, are:

- `conrad-temkin-2009-nonarchimedean-analytification`, Conrad–Temkin,
  *Non-archimedean analytification of algebraic spaces* (2009), Theorem 2.2.3,
  printed pp.7–8, and Example 2.3.2, printed pp.11–12. Source SHA256:
  `ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- `conrad-2011-weil-grothendieck-adelic-points`, Conrad,
  *Weil and Grothendieck approaches to adelic points* (31 December 2011),
  printed p.19, final paragraph of the proof of Proposition 5.11(3).
  Source SHA256:
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad–Temkin use rigid spaces; the Library's explicit affine space is a glued
Berkovich spectrum. The equation proved here is a derived formulation for the
Library's constructions. The four auxiliary lemmas are internal computations in
that model. The theorem retains arbitrary independent universes for `K`, `A`
and `B` and requires neither positive presentation arity nor nonzero algebras.
It proves the displayed equality of underlying points. Statements about
`FieldPoint` structures, topology, nonaffine spaces, presentation independence,
and extension of the ground field are outside its scope.
