# Singleton weak base change from the totally complex joint rank induction

In `Langlands.Automorphic.Unramified`,
`CyclicPrimeCuspidalBaseChangeExistenceTCReductionStatement` is the implication
from `CyclicPrimeJointRankInductionTCStatement` to
`CyclicPrimeCuspidalBaseChangeExistenceTCStatement`, using the same four
universe parameters `uF`, `uE`, `uV`, and `uW` in both propositions.
The theorem `cyclicPrimeCuspidalBaseChangeExistenceTC_of_jointRankInduction`
proves this implication. The all-ranks joint induction is an explicit
premise, to be supplied by the analytic rank step and strong induction.

The prime degree gives a generator of the Galois group, and
`HeckeCharacter.cyclicNormKernelCharacter` gives a character with the
idele class norm image as kernel. The proof chooses an actual representative
`S` of the lower cuspidal class. Singleton unitarity makes `S` unitarizable,
so its central character is unitary. The proof applies the going-up clauses
of the joint induction at the matrix rank of `S`.

When the norm-kernel determinant twist fixes the lower class, the
going-up clause directly gives the full Galois orbit of the upper class,
its unitarity, and its attached weak base change relation. In the other
case the clause gives an actual upper cusp with unitary central character
and an attached weak base change relation between classes. The Petersson
form theorem gives unitarizability of that cusp.
`IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff` identifies the class
relation with the relation between their singleton isobaric data.

The two witnesses implement the existence part of Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), III.4.2(a)–(b), printed p. 202 and pp. 203–206.
The proof of III.4.2(c) on printed p. 206 uses these cases on each
constituent. The registered source is `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
