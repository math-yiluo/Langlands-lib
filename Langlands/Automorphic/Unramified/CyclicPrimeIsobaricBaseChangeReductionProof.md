# Prime cyclic isobaric weak base change from the joint rank induction

`Langlands.Automorphic.Unramified.cyclicPrimeIsobaricBaseChangeReduction` proves
`CyclicPrimeIsobaricBaseChangeReductionStatement` with its four universe
parameters `uF`, `uE`, `uV` and `uW` and its published hypotheses. The premises
are `CyclicPrimeJointRankInductionStatement` and upper Euler constituent
recovery, `CuspidalEulerConstituentRecoveryStatement.{uE, uW}`. The conclusion is
`CyclicPrimeIsobaricBaseChangeStatement`, where the number fields may have real
places.

## The proof

`exists_unitary_weakBaseChange_ofCuspidal_of_jointRankInduction` treats one
unitary cuspidal class `c` over `F`, for a Galois extension `E/F` of prime
degree. The Galois group has prime order, so it is cyclic; choose a generator
`σ`. `HeckeCharacter.cyclicNormKernelCharacter` supplies a Hecke character `η`
whose kernel is the norm subgroup. Choose an actual cuspidal realization `S`
representing `c`. The singleton datum of `c` is unitary, so `S` is
unitarizable (`IsobaricData.isUnitary_ofCuspidal`), and then its central
character is unitary
(`CuspidalOperatorRealization.hasUnitaryCentralCharacter_of_isUnitarizable`).
The joint rank induction at the matrix rank of `S` gives the going-up clauses
`CyclicPrimeGoingUpAtRank` for `S`.

- If `η` fixes the class of `S` as a determinant twist, the second clause gives
  an upper cusp whose full Galois orbit is unitary and is a weak base change of
  the singleton datum of `c`.
- Otherwise the first clause gives an upper cusp `T` with unitary central
  character whose class is a weak base change of the class of `S`. The
  theorem `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  makes `T` unitarizable, so its singleton datum is unitary, and
  `IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff` turns the relation between
  classes into the relation between singleton data.

In both cases the witness is actual unitary isobaric data over `E` with
attached finite-place spectra.

`cyclicPrimeIsobaricBaseChangeReduction` takes a unitary isobaric datum `DF`.
`IsobaricData.exists_unitary_weakBaseChange_of_singletons`, applied to the
singleton lifts above, adds them up to a unitary datum `DE` over `E` that is a
weak base change of `DF`. Any other weak base change of `DF` equals `DE` by
`IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecovery` from the
module `Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeUniquenessProof`,
applied with the supplied recovery over `E`. That uniqueness needs no
unitarity, so it covers in particular the unitary competitors in the
statement.

The totally complex counterparts are
`cyclicPrimeCuspidalBaseChangeExistenceTC_of_jointRankInduction` and
`cyclicPrimeIsobaricBaseChangeTC_of_singletons`. The argument here is the same,
and none of its steps uses the totally complex hypothesis.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Theorem III.4.2, printed p. 202 (PDF p. 216): parts (a) and (b) are the two
cuspidal cases, according to whether the cuspidal representation is isomorphic
to its twist by `η`, and part (c) is existence and uniqueness of the lift of a
representation induced from cuspidal. The proof of (c), printed p. 206
(PDF p. 220), applies (a) or (b) to each cuspidal constituent and then
induces; uniqueness comes from (2.4), printed p. 200 (PDF p. 214). Here the
going-up clauses of `CyclicPrimeJointRankInductionStatement` stand for (a)
and (b), the sum of isobaric data stands for the induction, and the recovery
premise stands for (2.4).
