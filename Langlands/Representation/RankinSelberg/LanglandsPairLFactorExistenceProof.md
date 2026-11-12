# Existence of the L-factor of every irreducible admissible pair

Author: Worker 5010.

`Langlands.RankinSelberg.langlandsPairLFactorExistence` proves exactly the
published proposition
`Langlands.RankinSelberg.LanglandsPairLFactorExistenceStatement.{uF,uV,uW}`
of `Langlands/Representation/RankinSelberg/LanglandsQuotientLFactorStatement`.
The theorem has no outer parameters and no hypotheses. Every quantifier of the
statement stays inside it: the prime `p`, the p-adic field `F` with its
canonical topological data, the unitary additive character `ψ`, the supplied
self-dual Haar measure `ν : SelfDualHaar F.canonicalTopologicalData ψ`, the
ranks `r + 1` and `t + 1` in either order, and smooth `π` and `σ` with carriers
in `Type (max uF uV)` and `Type (max uF uW)`, together with their
irreducibility and admissibility. The field universe `uF` and the two
block-carrier universes `uV` and `uW` stay independent. The statement pair and
everything it imports are unchanged; only this proof pair is added.

## What is constructed

For each such pair the proof produces an actual polynomial `P` and a proof of
`IsLanglandsPairLPolynomial.{uF,uV,uW} F ψ ν.val π σ P`. The relation has
three parts, and the proof supplies each one:

- a tempered Langlands datum of `GL_(r+1)(F)` with blocks in `uV` that has
  `π` as an irreducible quotient of its standard module;
- such a datum of `GL_(t+1)(F)` with blocks in `uW` for `σ`;
- for every pair of data presenting `π` and `σ`, `P` is the symmetric
  L-polynomial `IsPadicSymmetricLPolynomial F ψ ν.val` of their two standard
  modules.

`P` is the integral-based L-polynomial of one actual pair of standard modules.
It is not taken from a supplied certificate. The proof adds no
classification, exhaustion, Whittaker-type or analytic-existence premise, and
it does not restrict to generic pairs.

## Implemented proof

The proof uses four published theorems.

1. `Langlands.glRegularLanglandsExhaustion.{uF,uV}` (module
   `Classification/RegularLanglandsExhaustionProof`) proves
   `GLRegularLanglandsExhaustionStatement.{uF,uV}`. It is applied with the
   canonical topological data `F.canonicalTopologicalData`, the positive rank
   `r + 1` (`Nat.succ_pos r`), and the irreducibility and admissibility of
   `π`. It returns a datum
   `d : TemperedLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData (r + 1)`
   with `d.IsLanglandsHead π`. The statement's admissibility hypothesis
   `SmoothRep.IsAdmissible π` is by definition
   `Langlands.IsAdmissible π.representation`, which is what this theorem takes.
   The same theorem at `.{uF,uW}` gives `e` for `σ`. The blocks of `d` and `e`
   lie in the saturated universes `max uF uV` and `max uF uW`.
2. `Langlands.RankinSelberg.langlandsTypeLFactor.{uF, max uF uV, max uF uW}`
   (module `RankinSelberg/LanglandsTypeLFactorProof`) proves
   `LanglandsTypeLFactorStatement` at these saturated universes. Applied to
   `p, F, ψ, ν, r, t, d, e`, it gives a polynomial `P` with
   `IsPadicSymmetricLPolynomial F ψ ν.val d.standardModule.representation
   e.standardModule.representation P`. The block polynomials and the product
   formula it also returns are not used.
3. `Langlands.glRegularLanglandsDataUniqueness` at `.{uF,uV}` and `.{uF,uW}`
   (module `Classification/RegularLanglandsDataUniquenessProof`) proves the
   two `GLRegularLanglandsDataUniquenessStatement` inputs.
4. `Langlands.RankinSelberg.isLanglandsPairLPolynomial_of_saturatedData`
   (module `RankinSelberg/LanglandsPairLPolynomialReduction`) takes these two
   uniqueness proofs, the saturated data `d` and `e`, the quotient relations
   `hd.isLanglandsQuotient` and `he.isLanglandsQuotient`
   (`TemperedLanglandsDatum.IsLanglandsHead.isLanglandsQuotient`), and the
   certificate for `P`. It returns
   `IsLanglandsPairLPolynomial.{uF,uV,uW} F ψ ν.val π σ P` with the same `P`.

The last theorem works as follows (see
[LanglandsPairLPolynomialReduction](LanglandsPairLPolynomialReduction.md)).
`TemperedLanglandsDatum.exists_realization` replaces the saturated blocks by
equivalent irreducible blocks with carriers in the original `uV` and `uW`.
The equivalences of standard modules carry the quotient relations and the
L-certificate across, so these realized data are the two existential
witnesses. For any other presenting data `d'` and `e'`, data uniqueness makes
the standard modules equivalent, and `IsPadicSymmetricLPolynomial.congr_equiv`
moves the certificate for `P` to `d'.standardModule` and `e'.standardModule`.
This gives the universal clause.

The `lean_check` inspection of the theorem reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source and normalization

The target is the sentence after display (4) of Jacquet, Piatetski-Shapiro
and Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983),
§(9.4), printed page 458, registered as `jpss-1983-rankin-selberg` (SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). I
checked that page as an image (one-based PDF page 93). The source says that
an irreducible admissible `π` (resp. `σ`) "is uniquely representable as a
quotient of a representation `ξ` (resp. `η`) of Langland's type", and that
"one can take (4) as a definition of `L(s, π × σ)` for any pair `π, σ` of
irreducible, admissible representations". Here `L(s, ξ × η)` is the factor of
display (3).

The proof matches each part of that sentence with a published result:

- existence of the representation as a quotient is
  `glRegularLanglandsExhaustion`;
- its uniqueness is `glRegularLanglandsDataUniqueness`;
- the existence of `L(s, ξ × η)` for the standard modules is
  `langlandsTypeLFactor`.

The normalizations are those of the statement:

- `L(s, π × σ) = 1 / P(q^(-s))`, with `q` the residue cardinality of
  `F.canonicalTopologicalData`;
- the pair is read with the larger rank first, as in JPSS (2.12)
  (`IsPadicSymmetricLPolynomial`);
- standard modules are normalized induction from the upper block parabolic of
  irreducible analytically tempered blocks twisted by `|det|^(u_i)` with
  strictly decreasing real `u_i`;
- `ν` is the supplied self-dual Haar measure, used through `ν.val`.

The proof does not follow the source's argument. JPSS take the
classification from the literature, and this proof uses the Library's proved
classification theorems instead. The Markdown of those theorems gives their
own sources: Silberger 1978, Theorem 4.1, and Kudla 1994, §2.2. The proof of
display (3) is described in
[LanglandsTypeLFactorProof](LanglandsTypeLFactorProof.md).

## Scope

This unit proves only `LanglandsPairLFactorExistenceStatement`. The other
statements of the same module are separate units and are not claimed here:
`GenericLanglandsQuotientLFactorStatement`,
`SquareIntegrableDataLFactorStatement`, and their conjunction
`LanglandsQuotientLFactorStatement`. The same holds for nongeneric epsilon
factors.
