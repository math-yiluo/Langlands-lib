# The unitary bound for two real discrete blocks

`RealRankFourUnitaryBoundStatement` concerns the \(O(4)\)-finite standard module
of two unlinked real discrete blocks of the same positive absolute weight
with exponents \(u+a\) and \(u-a\), where \(u\) is complex and \(a\) is real.
An invariant positive form on this module implies \(|a|<1/2\).

The proof equips the algebraic carrier with the inner product of the given
form. The real matrices of the trace-dual basis act skew-adjointly. On the
compact highest vector the weight for the left compact triple is
\(m=|\mathrm{weight}|+1\), and the right compact triple annihilates the vector.
The trace-free Casimir eigenvalue is \((m-1)^2+4a^2-5\). The three column
estimates in `RealRankFourEnergy` applied to this vector give
\(4a^2\leq 1\).

Equality would give an exponent difference of \(1\) in one of the two
directions. The equal-weight linkage criterion declares this pair linked.
Applying `AreRealBlocksUnlinked` to the two discrete Mœglin data rules out
equality.

The strict range agrees with the two-block part of Badulescu and Renard
(2010), Theorem 8.2, p. 1131 (PDF p. 18). The endpoint in their Proposition
9.4, p. 1133 (PDF p. 20), corresponds to the equal-weight specialization of
Mœglin (1997), Theorem 10b, condition (iii), pp. 164–165 (PDF pp. 173–174).
The compact highest vector and Casimir energy estimate give a direct
derivation of the weak bound in the positive form model of Knapp and Vogan
(1995), Introduction §1, display (0.5), p. 6 (PDF p. 28).
