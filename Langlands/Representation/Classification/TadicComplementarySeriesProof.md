# Proof of Tadić's complementary-series proposition

Author: Worker 5219.

The module `Langlands.Representation.Classification.TadicComplementarySeriesProof`
proves `Langlands.Classification.ComplementarySeriesUnitarity.{uF, uV} F T` (Tadić 1986,
Proposition 2.9) for every prime `p`, every `F : PadicField.{uF} p` and every
`T : F.TopologicalData`. The universes `uF` and `uV` are independent. The theorem is
`Langlands.Classification.complementarySeriesUnitarity`. It adds no hypotheses, and its
axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Proof, as implemented

The proof is one line. It applies the bridge
`Langlands.Classification.complementarySeriesUnitarity_of_characterLimit`
(module `TadicComplementaryEndpointBridge`, added with this proof and described in
its own Markdown) to the Library theorem `Langlands.unitaryCharacterLimitSubquotients`,
which proves `Langlands.UnitaryCharacterLimitSubquotientsStatement`. The universe pair
is `{uF, max uF uV}`, the universes of the actual general linear group and of its
representations.

- The open-interval clause comes from the Library lemma
  `complementaryProduct_unitarizableOnInterval` through the bridge.
- In the end-point clause, the bridge approximates the end point `a` by
  `a - a/(k+1)` inside the interval. The resulting products are irreducible,
  admissible and unitarizable, and their distribution characters converge to that
  of the end-point product. The end-point product is admissible and of finite
  length. The character-limit theorem then shows that every irreducible
  subquotient of the end-point product is unitarizable.

## Provenance of the ingredients

All ingredients other than the bridge are already in the Library and are imported
by Lean name.

- `Langlands.unitaryCharacterLimitSubquotients` (module
  `Langlands.Representation.Unitary.CharacterLimitSubquotientsProof`, Worker 5667)
  uses the corner-form gluing theorem `Langlands.CornerFormGluing.cornerFormGluing`
  (Worker 4713) and the positive trace-form construction in
  `Langlands.LinearAlgebra.PositiveTraceForms` (Worker 5219).
- The admissibility, finite-length and character-continuity lemmas for the
  complementary product are in `TadicComplementaryEndpointHelpers`, and the
  open-interval unitarity is in `TadicComplementarySeriesUnitarityProof`.

## Comparison with the source

Tadić's proof of Proposition 2.9 (Ann. Sci. ENS (4) 19 (1986), p.350) obtains the
end-point clause from his Theorem 2.7 on limits of characters of unitary
representations, together with Bernstein's Proposition 8.3 and his Lemma 2.8. The Lean
proof follows the same outline. The Library character-limit statement it uses is the
all-constituent form of Theorem 2.7(i), stated for unimodular totally disconnected
groups with a given admissible finite-length limit; its own Markdown compares it with
the source.
