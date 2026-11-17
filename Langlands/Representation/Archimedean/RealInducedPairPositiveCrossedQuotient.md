# An actual positive-inner quotient onto the crossed induction pair

This internal construction proves an exact surjective intertwiner from the
actual compact-finite module of a linked pair of real induction blocks onto
its heavier crossed endpoint pair. Its assumptions are positive original
absolute weights `L,M`, the linked equality at a natural index `k`, and
positive signed inner weight `H`. It uses no additional squared-weight bound,
classification input or assumed map/range premise.

Use the original endpoint parities `L%2,H.toNat%2` from
`RealInducedPairCrossedMiddleQuotient`, and write `u,v,x,y` for their lower
and upper endpoints. The actual middle tail maps the ascending
four-character presentation `[u,v,x,y]` exactly and surjectively onto
the mixed source `J=[u,induced(v,x,H),y]`. Its explicit right inverse is the
existing inner section. The tail's symmetry is `(-1)^H`; thus the proved
ambient polynomial Fourier propagation bounds its adjacent windows.

The earlier crossed mixed quotient `U:J→CrossedPair` is exact and onto.
Compose it with the middle tail to obtain `F` from the original character
presentation. To descend `F` through the original two-block quotient, the
proof kills both of that quotient's explicit binomial kernel generators.

The first binomial image has Fourier support `|j|<L` at position zero.
The middle tail expands this to `|j|<L+H`, and the crossed first tail, of
cutoff `A=L+H`, kills it. The second binomial image similarly has support
`|j|<M` at position two; after the middle tail this lies below the crossed
second cutoff `B=M+H`. The crossed quotient's kernel contains both such
binomial ranges. The actual mixed-source inclusion is the identity on
underlying functions, so the same coefficient bounds apply after inclusion.

The published split original quotient now descends `F` to the explicitly
defined map `quotient`. Its factorization and unchanged range prove both
exact intertwining and surjectivity. The crossed arithmetic gives preserved
support and squared-weight increase `2HP>0`, so the target crossed pair is
an allowed heavier adjacent piece.

`RealInducedPairPositiveCrossedQuotientStatement` asserts this exact
surjective quotient and the heavier-piece property for every input with
the stated hypotheses. `realInducedPairPositiveCrossedQuotient` proves it.
This is a quotient *from* the original module. To obtain the desired
filtration, its kernel must still be identified with a span of earlier
allowed source images. This module proves no such kernel equality and does
not prove `RealInducedInducedFiltrationStatement`.
