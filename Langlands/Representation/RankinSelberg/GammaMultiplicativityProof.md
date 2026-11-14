# Gamma multiplicativity for normalized block induction

Worker 20 authored this internal assembly of published results.
`Langlands.RankinSelberg.gammaMultiplicativity` proves exactly
`GammaMultiplicativityStatement.{uF,uV,uW}` from
`Langlands.Representation.RankinSelberg.MultiplicativityStatement`.
For every ordered family of positive-rank blocks it constructs rational functions
`G i`, certifies each original block pair by
`IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)`, and certifies their
product for the actual
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`.
The field, test carrier and dependent block carriers retain independent universes.
The theorem retains every canonical p-adic field, the supplied nontrivial unitary
additive character and self-dual Haar measure, all positive ranks in both orders,
and arbitrary full Whittaker-type inputs, including reducible representations.

The Lean term applies the published finite-block reduction
`gammaMultiplicativity_of_twoBlock` to the published closed theorem
`twoBlockGammaMultiplicativity` twice. The first instance has universes
`.{uF,uV,uW}`; the second has `.{uF,uV,max uF uW}`. The second block-carrier
universe is needed because an actual normalized induced tail has carrier
universe `max uF uW`. Both premises are discharged by the same closed theorem;
there is no additional hypothesis on induction, factor existence or universes.

The imported finite reduction inducts on the number of ordered blocks. An empty
family contradicts the positive total rank. For a singleton, the two-block theorem
applied to a duplicated block supplies a certified factor for the original pair;
`singleBlock_gamma_iff` transfers it to actual singleton normalized induction.
For more blocks, induction supplies the tail factors and their product
certificate. `normalizedProductWhittakerType` proves the full Whittaker type of
the actual induced tail. The reduction uses total-rank substitution and
representation-equivalence invariance of the complete functional space to place
the original head and induced tail in the second two-block instance.

The two-block conclusion then gives head, tail and outer induced certificates.
Symmetric gamma certificate transport returns the head to its original carrier.
Certificate uniqueness identifies the new tail factor with the product already
obtained by induction. `headTailProductInductionEquiv` transfers the outer
certificate to the original actual ordered induction. The successor product
formula assembles the original family of block factors and the required product.
These are the steps implemented in `FiniteGammaMultiplicativity`; this module
closes its two displayed premises without changing that proof.

The imported two-block theorem supplies complete certified factors through the
two rank descents of JPSS Sections 7.1–7.2. It uses the published full-type
induction, gamma construction, equal-rank exchange, dominant-rank, adjacent-rank,
rank-one test and rank-one full-type proofs, followed by transport of the entire
actual dependent family back to independent universes. Its upper-convention
analytic bases implement the source's lower-to-upper comparison by reversing
ordered sizes, dependent carriers and actions together and transporting complete
certificates through actual normalized induction equivalences. The finite
head/tail grouping preserves ordered coordinates and the positive half modulus.

The mathematical source is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), Theorem 3.1(i), printed pages 404–405.
Section 3.2, printed page 405, reduces the finite family to two blocks by
induction; Sections 7.1–7.2, printed pages 438–442, supply the two-block gamma
descents. The registered original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original proof and registered errata were checked during the prerequisite
development; no applicable registered erratum was found. The implementation
here derives the exact existing proposition solely from the two imported
published results. The target pair and its imports are unchanged.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
