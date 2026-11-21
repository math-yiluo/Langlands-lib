# Character-detecting stabilizer paths on the nonopen complex Bruhat cells

`ComplexJacquetBoundaryStabilizerStatement` applies at each point of an
upper Bruhat cell indexed by a permutation other than the long element.
It gives a pair of paths in the upper unipotent group. Left multiplication
by the first path and right multiplication by the second fix the given
point. Each path has matrix entries of the form \(1+tX\) for a fixed
square-zero direction \(X\). For the Fourier parameter \(a\) in the
Whittaker character, the right path has character
\(\exp(4\pi i t)\).

A permutation other than the reversal has an adjacent ascent, since a
strictly decreasing permutation is the reversal. The transvection for
this adjacent position is upper unipotent before and after conjugation
by the permutation matrix. At a point with Bruhat coordinates
\(g=bwv\), the right path is this transvection conjugated by \(v^{-1}\),
and the left path is its inverse conjugated by \(bw\). Conjugation by an
upper triangular matrix preserves the upper unipotent condition. The
stabilizer equation follows by cancellation. The increments of the
transvections square to zero and conjugation preserves this identity.
The sum of first-superdiagonal entries is invariant under upper unipotent
conjugation, so the right character equals the trace character of the
original transvection. Its parameter is \(t/a\), giving the displayed
exponential.

This is the complex matrix form of the generic stabilizer calculation
in Casselman, Hecht and Miličić, *Bruhat filtrations and Whittaker vectors
for real groups* (2000), §6, proof of Lemma 6.7 on p. 178.
