# Discrete-series orbit finiteness by relative semisimple rank

`RationalExactRankDiscreteSeriesOrbitFinitenessStatement n` specializes
the local form of Waldspurger VIII.1.2 to connected reductive groups of
relative semisimple rank `n`. It measures rank as the dimension of the
relative root span for a maximal split torus. The local conclusion
retains every split component, quotient Haar measure and compact open
level. The field and representation carrier universes are independent.

Waldspurger's induction paragraph on printed p. 321 uses both VIII.1.1
and VIII.1.2 at strictly smaller ranks. For the finiteness part,
`rationalStrictlyLowerRankOrbitFiniteness_succ_iff` extends the strict
bound from `n` to `n + 1` by adjoining the assertion for exact rank `n`.
Its proof splits the natural-number inequality into strict inequality
and equality. At bound one,
`rationalStrictlyLowerRankOrbitFiniteness_one_iff` identifies the premise
with the existing rank-zero target. The global VIII.1.2 statement is
equivalent to the family of bounded statements. The reverse implication
uses `exists_maximalSplitTorus` for the actual group and takes the bound
to be one larger than the rank of the resulting torus.

Remark VIII.1.3 uses finiteness for the semistandard Levis to control
spectral support. Once the bound includes the ambient rank,
`RationalSemistandard.allLeviOrbitFiniteness_of_rank_lt` supplies its
all-Levi finiteness premise. The inherited maximal split torus acts on
each closed reductive Levi model through its inclusion into the ambient
group. The Levi's relative roots therefore form a subset of the
ambient roots in the same character lattice. Monotonicity of the
dimension of their rational spans bounds the Levi rank. Before the
ambient finiteness step, the existing proper-Levi adapter uses strict
rank decrease and the earlier bound.

These deductions organize the finiteness input to the induction.
The rank-wise finiteness proofs and the local synthesis reconstruction
used in VIII.2.1 are separate analytic obligations.
[Waldspurger (2003), VIII.1.2–VIII.2.1, printed pp. 321–322](https://doi.org/10.1017/S1474748003000082)
