# Smoothness and connectedness of anti-affine algebraic groups

`Langlands.GroupScheme.AntiAffineSmoothConnectedStatement.{u}` states the
smoothness and connectedness clauses of SGA 3, Exposé VI_B, Lemma 12.3, printed
page 431 / PDF page 101, Gille–Polo recomposed edition of 13 October 2024.
The complete official Tome I errata of the same date do not change this lemma.

For every field `k : Type u` and actual group scheme `N` over `Spec k`, local
finite type, quasi-compactness, and the unchanged `IsAntiAffine N` imply
smoothness and connectedness. Here anti-affineness says that the actual
structure morphism induces an isomorphism on global functions. The two
geometric assumptions express that `N` is an algebraic group; separatedness
is automatic for field group schemes by the published `fieldSeparated`.
There is no perfectness or algebraic-closedness assumption, and the initial
group need not be smooth or connected.

The source additionally concludes commutativity. This supporting statement
only retains the two clauses required for `AntiAffineQuotientExistenceStatement`.
Its scope includes the full scheme-theoretic kernel after anti-affineness of
that kernel has been proved. The proposition does not assume a represented
quotient, an affine ambient group, or a reduced source. This file is a
statement definition and supplies no proof.

Source identifier: `sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
