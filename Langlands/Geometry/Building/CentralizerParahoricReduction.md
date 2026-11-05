# Reduction of the centralizer part to singleton sharp fixers

Module `Langlands.Geometry.Building.CentralizerParahoricReduction`.
This is a derived reduction of the exact published
`ParahoricBuildingData.CentralizerParahoricIntersectionStatement`.
It retains the actual centralizer inclusion, the actual subgroup `Z(F)^0`,
arbitrary universe `u`, both local-field characteristics, and the corrected
apartment-axiom premise. It does not prove KP Lemma 7.4.3.

## Statement and implemented proof

`CentralizerParahoricReductionStatement` says that the published target is
equivalent to

```
P.apartment.SatisfiesApartmentAxioms P.centralizer →
  ∀ x : P.Apartment, centralizerPoints P.i ⊓ P.sharpFixer {x} ≤
    P.centralizerZero.map (rationalPoints.map P.centralizer.j)
```

The theorem `centralizerParahoricReduction` proves this equivalence.
The singleton inclusions on its right remain to be proved.

The helper `map_centralizerZero_le_centralizerPoints` uses the representing
centralizer inclusion to put each actual image point into the centralizer.
Together with the defining inclusion into a parahoric, it gives
`map_centralizerZero_le_centralizer_inf_parahoric`, the immediate inclusion
of the target equality. This helper works for empty subsets as well.

For any subset `Ω`, `centralizer_inf_parahoric_eq_iff` proves that the full
intersection equality is equivalent to the sharp intersection inclusion.
One direction follows from the inclusion of the sharp fixer into the
parahoric. For the other, `KPParahoricProduct.mem_parahoric_iff` writes an
element as `j(z) * h`, with `z ∈ Z(F)^0` and `h ∈ sharpFixer Ω`.
If this product centralizes the torus, then so does `h`, since `j(z)`
already does. The assumed sharp intersection inclusion puts `h` in
`j(Z(F)^0)`; closure under multiplication gives the required full inclusion.
The factorization theorem uses the previously proved normalization of
sharp fixers by the actual zero subgroup.

Finally, `centralizer_inf_sharpFixer_le_of_mem` uses
`KPApartmentData.sharpFixer_anti`: if `x ∈ Ω`, then
`sharpFixer Ω ≤ sharpFixer {x}`. The forward implication of the main
equivalence specializes the original target to `{x}`; the reverse chooses
a point from the given nonempty subset and uses these two helpers.
No compactness, boundedness, cover transport, or equality between norm-one
and zero subgroups is assumed or proved here.

## Provenance

The equivalence is an internal derived statement, obtained by subgroup
algebra and antitonicity from the existing definitions. It is not asserted
to be a separately numbered statement in the literature.
The mathematical target and product definition come from Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Definition 7.4.1 and Lemma 7.4.3, printed p. 255 / PDF p. 286.
The underlying sharp-fixer definition is Definition 7.4.1(2).
The zero subgroup remains the one from Definition 2.6.23.
The target's corrected premise is retained from the published statement;
the corrections of 1 November 2024, source ID
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 33, add AS 5 to Chapter 7.
