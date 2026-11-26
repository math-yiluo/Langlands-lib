# Proof of the cyclic regular-induction existence reduction over a totally complex base

Module `Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceReductionTCProof`.

## Result

`Langlands.Automorphic.Unramified.cyclicRegularInductionExistenceReductionTC :
CyclicRegularInductionExistenceReductionTCStatement.{uF, uE, uV, uW}`, the exact
totally complex target of module `CyclicRegularInductionExistenceReductionStatement`,
for arbitrary universes `uF`, `uE`, `uV`, `uW`. No hypothesis is added, and no
axiom beyond `propext`, `Classical.choice` and `Quot.sound` is used. Each of the
eleven premises is used, at its stated universe levels.

## Proof

The proof introduces the eleven premises, a totally complex number field `F`, a
Galois extension `E`, and applies the common argument
`CyclicRegularInductionExistence.cyclicRegularInductionExistenceOver_of_inputs`
of `CyclicRegularInductionExistenceReductionProof`, whose Markdown describes it:
strong induction on `[E : F]`, with the degree-one transport, the prime step through
the pair count and the reverse orbit comparison, and the composite step through the
fixed field `K` of a subgroup of prime order.

The common argument asks for the prime realization, the pair comparison and Euler
constituent recovery only over `F` itself and over number fields carrying an algebra
over `F`: the intermediate field `K` and the upper field `E`. Every such field is
totally complex, by `NumberField.isTotallyComplex_of_algebra`, since all infinite
places of `F` are complex. So these inputs are supplied by the totally complex
premises:

- `CyclicPrimeRegularOrbitRealizationTCStatement` and
  `CyclicWeakBaseChangePairMultiplicityTCStatement` at `.{uF, uE, uV, uW}`, over `F`;
- the same two premises at `.{uE, uE, uW, uW}`, over the intermediate field;
- `CuspidalEulerConstituentRecoveryTCStatement` at `.{uE, uW}`, over the upper field.

The reverse orbit comparisons `CyclicOrbitBaseChangeWeakInductionStatement`,
weak base-change equivariance, transitivity of weak induction and the two attachment
premises are unrestricted and are passed unchanged.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`, proof of
Lemma III.6.4, printed pp. 217–218 (PDF pp. 231–232), with Theorem III.4.2(e),
printed pp. 202 and 207–210 (PDF pp. 216 and 221–224), III.(2.2)–(2.4), printed
p. 200 (PDF p. 214), Proposition III.4.4(iii), printed pp. 210–211 (PDF pp. 224–225),
and Definition III.6.1 and Theorem III.6.2, printed pp. 214–217 (PDF pp. 228–231),
in the form described in `CyclicRegularInductionExistenceReductionProof.md`.
