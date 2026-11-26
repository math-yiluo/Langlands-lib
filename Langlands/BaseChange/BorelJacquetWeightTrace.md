# Trace of a uniformizer diagonal on the normalized Borel Jacquet fixed space

Let \(W\) be the integral-diagonal fixed space in the normalized upper
Borel Jacquet module of a complex representation of
\(\mathrm{GL}_{r+1}(F)\). For finite-dimensional \(W\),
`BorelJacquetWeightTraceStatement` computes the trace on \(W\) of the
normalized action of \(\operatorname{diag}(\varpi^{\nu_i})\).
The result is
\[
  \sum_{c \in \mathrm{JacquetMultiset}} \prod_{i=0}^r c_i^{\nu_i}.
\]
The sum counts each tuple with its generalized weight multiplicity and
allows every integer exponent.

`borelJacquetLatticeAction` restricts the normalized Jacquet action of the
canonical uniformizer diagonal to \(W\). The diagonal preserves \(W\)
because it commutes with the integral diagonal subgroup. The lattice
generators act by `borelJacquetUniformizerAction`, so the joint
generalized blocks are exactly `borelJacquetWeightSpace`. The proof uses
`commutingTupleGeneralizedWeightGlobalBasis` to compute the diagonal of
the action in a basis assembled from these blocks. Each basis vector
in the block at \(c\) contributes the character value
\(\prod_i c_i^{\nu_i}\). Regrouping the finite diagonal sum gives the
sum over `borelJacquetMultiset`.

The companion lemma `borelJacquetLatticeAction_apply_eq_of_ord` identifies
the normalized action of every diagonal with orders \(\nu_i\) with the
same lattice action on \(W\). Dividing each entry by the corresponding
canonical uniformizer power gives an integral diagonal unit, which
acts trivially on \(W\).

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ
en caractéristique non nulle* (2011), I.5.4, Lemma 2 and its proof,
printed p. 35, use this multiplicity sum for the normalized Jacquet
action in the regular elementary trace formula. The proof here computes
the normalized diagonal trace directly from the generalized blocks on
the integral-diagonal fixed space.
