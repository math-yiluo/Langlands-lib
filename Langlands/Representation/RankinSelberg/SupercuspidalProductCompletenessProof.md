# Whittaker completeness against normalized products of supercuspidals (proof)

This module proves `Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement.{uF, uW}`
for arbitrary universes `uF` and `uW`, as the theorem
`Langlands.RankinSelberg.supercuspidalProductCompleteness`. It adds no hypotheses.

## Statement proved

Fix a prime `p`, `F : PadicField p` with its canonical topology, a unitary additive character `ψ`,
an index `n`, and a quotient measure `μ` on `N_(n+1) \ GL_(n+1)(F)` compatible with
`generalLinearHaar` and `unipotentHaar`. Let `H` be a `ψ`-Whittaker function satisfying
`IsCompactWhittakerTestFunction`. Assume `∫ H f dμ = 0` for every test `f`. A test consists of:
- a block shape `(m_1+1, …, m_k+1)` of `n+1`;
- smooth irreducible supercuspidal representations `τ_i` of `GL_(m_i+1)(F)` on carriers in
  universe `uW`;
- an inverse-character Whittaker functional `ℓ'` of
  `canonicalNormalizedProductInduced (succBlockShape m h) τ`;
- a function `f` in its coefficient model.

Then `H = 0` (Henniart 1993, Lemme 2.1).

## Proof

The theorem is
`SupercuspidalCompleteness.supercuspidalProductCompleteness_of gelfandGraevJacquet deltaPairing`.
It combines three results.

- `SupercuspidalCompleteness.supercuspidalProductCompleteness_of` (module
  `RankinSelberg.SupercuspidalCompleteness.Assembly`). It derives the statement from two
  propositions, `GelfandGraevJacquetStatement` and `DeltaPairingStatement.{uF, max uF uW}`.
  1. Suppose `H ≠ 0` and convert `H` into a nonzero element `h` of the Gelfand–Graev
     representation `c-Ind_N^G ψ` (module `Conversion`).
  2. Module `FrobeniusDetection`, using `GelfandGraevJacquetStatement` and the cuspidal
     detection in the Levi Gelfand–Graev representation, gives:
     - a block shape `B`;
     - irreducible supercuspidal `A_i`;
     - an intertwiner `Tf` from `c-Ind_N^G ψ` to the normalized parabolic induction of the
       `A_i`, with `Tf h ≠ 0`.
  3. A smooth functional detecting `Tf h` gives a vector in the smooth dual. The dual is
     identified with the normalized induction of the contragredients
     (`CuspidalProductContragredient`), and the contragredients are again irreducible and
     supercuspidal.
  4. The resulting invariant pairing is an integral against Whittaker coefficients, by
     `DeltaPairingStatement`. The hypothesis on `H` then forces `ℓ(Tf h) = 0`, which is a
     contradiction.
- `Whittaker.gelfandGraevJacquet` (module `Whittaker.GelfandGraevJacquetOpen`). It proves
  `GelfandGraevJacquetStatement`: the normalized Jacquet module of `c-Ind_N^G ψ` along a standard
  block parabolic is equivalent to the Levi Gelfand–Graev representation.
  1. The Mackey filtration of the restriction to `P` collapses to the open orbit piece
     (`Whittaker.gelfandGraevJacquet_of_openPiece`, module `Whittaker.GelfandGraevJacquet`).
  2. The open orbit piece, that of the double coset `N w⁻¹ P` with `w` the block-reversal
     matrix, is identified by compact induction in stages and integration over the unipotent
     radical (`Whittaker.gelfandGraevOpenPiece`).
- `SupercuspidalCompleteness.deltaPairing` (module
  `RankinSelberg.SupercuspidalCompleteness.DeltaPairingGL`). It proves `DeltaPairingStatement`
  for every universe, in particular for `max uF uW`.

## Provenance

The target is Henniart 1993 (`henniart-1993-epsilon-pairs`), *Caractérisation de la
correspondance de Langlands locale par les facteurs ε de paires*, Lemme 2.1 (printed page 342).
It is attributed there to Jacquet–Shalika 1985, Lemma 3.2, and to
Jacquet–Piatetski-Shapiro–Shalika, *Conducteur des représentations du groupe linéaire*
(Math. Ann. 256, 1981), Lemma 3.5 (page 207).
The route implemented here is algebraic rather than the spectral (Plancherel) argument of the
sources:
- the Jacquet module of the Gelfand–Graev representation;
- cuspidal detection in the Levi Gelfand–Graev representation;
- Frobenius reciprocity;
- a delta-function identification of invariant pairings.

The supporting modules were written by Workers 1830 and 1832.
