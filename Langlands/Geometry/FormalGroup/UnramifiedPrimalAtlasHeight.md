# Height of the split primal atlas at ramification index one

The input is a split-special affine polarized framed point over a
nilpotent test with a square-height presentation of its primal frame.
The choice of primal factor is the one in Rapoport–Zink (1996), (6.17)
and the proof of Lemma 6.44, printed pp. 309–310 (PDF pp. 321–322).
Drinfeld (1976), §2 A, printed p. 109 (PDF p. 3), requires height \(d^2\)
for the special formal module of reduced degree \(d\).

Suppose \(p=u\varpi\) for an integral unit \(u\), and the central
residue cardinality is \(p^f\). On each chart the retraction of the
actual target supplies the finite locally free \(p^n\)-kernel. The
restricted primal rigidifier transfers the kernel rank from the
square-height frame. The unit \(u^n\) in \(p^n=u^n\varpi^n\) acts by
an automorphism. The natural equivalence of the two kernel functors
then uses the same representing finite locally free algebra for the
\(\varpi^n\)-kernel. `primalUnramifiedHeightAtlas` packages the chart
kernels and the resulting uniformizer height \(d^2\) on the same atlas.
