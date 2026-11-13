# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity` proves Whittaker multiplicity one for bundled local-field data. It also proves that this multiplicity one implies the exact-dimension statement for the unequal-rank compact generic pairing, over every nonarchimedean local field. The p-adic module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity` works over `F : PadicField p` with bundled topological data `T : F.TopologicalData`. Here `F` is an arbitrary field with bundled data `T : LocalFieldData F`: a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure (see `Langlands.LocalFieldData`).

Source: the target is the compact/generic case of the Lemma of Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), Section 2.11, p. 399, discussed on p. 403. Its line conclusion rests on the uniqueness of Whittaker functionals recalled in Section 2.1 of that paper. For every nonarchimedean local field, that uniqueness is the Library theorem `Langlands.Whittaker.localFieldMultiplicityOne` (Bernstein and Zelevinsky (1976), Theorem 5.16). This module is an internal assembly of Library results and makes no further literature claim.

## Declarations

- `Langlands.AllField.Whittaker.multiplicityOne` (theorem): proves the all-field `MultiplicityOneStatement.{uF, uV}`. For every field `F`, every `T : LocalFieldData F`, every rank `n + 1` and every unitary additive character `ψ`, the following holds under the topology `T.topology`. Every standard `ψ`-Whittaker functional on an irreducible admissible complex representation of `GL_(n+1)(F)` is a unique complex multiple of any given nonzero one.
- `Langlands.AllField.RankinSelberg.UnequalRankCompactPairing.inverseFunctionals_line_of_multiplicityOne` (theorem): assumes the all-field `MultiplicityOneStatement.{uF, uW}`. Under `T.topology`, any two Whittaker functionals for the inverse standard character of `ψ` on an irreducible admissible `η` are proportional when the first is nonzero.
- `Langlands.AllField.RankinSelberg.UnequalRankCompactPairing.unequalRankCompactGenericPairing_of_multiplicityOne` (theorem): assumes the all-field `MultiplicityOneStatement.{uF, uW}` and proves `UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r` for every `F`, `T`, `n` and `r`.

Multiplicity one is used for representation carriers in the same universe `uW` as the second representation of the pairing statement.

## Proof

- `multiplicityOne`: install the topology, the valuative relation and the local-field structure from `T` as instances. The goal is then exactly an instance of `Langlands.Whittaker.localFieldMultiplicityOne`, which is applied directly.
- `inverseFunctionals_line_of_multiplicityOne`:
  1. Install the instances from `T`. The topological-ring structure they provide makes `ψ.scale (-1)` a unitary additive character.
  2. By the published `Langlands.RankinSelberg.standardCharacter_scale_neg_one`, the inverse-standard functionals of `ψ` are exactly the standard functionals `glFunctionals (ψ.scale (-1)) n η` of `ψ.scale (-1)`.
  3. Multiplicity one for `ψ.scale (-1)` gives the scalar.
- `unequalRankCompactGenericPairing_of_multiplicityOne`: apply the ported `nonempty_equiv_complex_padic` of `UnequalRankCompactPairingFunctionals`. Admissibility gives the smoothness it needs. The line hypothesis comes from the previous theorem.

The original proof rewrites `T.topology` to the canonical normed topology of the p-adic field, using `topology_eq_canonicalNormTopology`, and then applies the p-adic multiplicity one. No such transport is needed here: every instance comes directly from `T`, and the multiplicity one used is the all-field Library theorem.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals`
- `Langlands.AllField.Representation.Whittaker.MultiplicityOneStatement`

The module also imports the Library module `Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof`.
