# Real generic standard parameters from classification and tied irreducibility

`RealGenericParameterFromTemperedStatement` takes two inputs. The
classification step takes a principal-series quotient to a quotient of
a Langlands-ordered standard module. Tied irreducibility asserts that a
standard module with constant real part of its block exponent is
irreducible. Together they imply the existence of a standard-module
parameter for every irreducible admissible generic real module.

Casselman's quotient theorem and the classification input give a
nonzero map from an ordered standard module. The real Levi integral
theorems and tied irreducibility give both its largest proper stable
subspace and the reverse-intertwiner kernel bound. With unlinked swaps,
the kernel bound proves irreducibility of an ordered standard module
with unlinked data. The known result for linked data excludes a
maximally faithful quotient there. Kostant's theorem and the
infinitesimal character of the generic module give maximal
faithfulness, so the quotient map is injective.

The quotient existence and exhaustion used in the classification input
come from Knapp, *Local Langlands correspondence: the archimedean case*
(1994), Theorem 1(a)–(b), printed p. 400 (PDF p. 410). The Lean order
uses the real part of the exponent \(t_j\) in the determinant twist
\(|\det|^{t_j}\), as in Getz and Hahn (2024), (10.29)–(10.31) and
Theorems 10.6.1–10.6.2, printed pp. 283–284 (PDF pp. 295–296). Knapp's
printed (2.5) divides the real exponent by the block rank \(n_j\).
The chamber computation for Knapp's determinant convention (2.2) is
given under `IsRealLanglandsOrdered` in
[RealGenericParameterReduction.md](RealGenericParameterReduction.md).

The generic injectivity route combines Kostant, *On
Whittaker vectors and representation theory* (1978), Theorem 3.9,
printed p. 142 (PDF p. 42), and Vogan, *Gelfand–Kirillov dimension
for Harish-Chandra modules* (1978), Theorem 6.2 and its implication
(a) to (f), printed pp. 89, 93 (PDF pp. 15, 19). The Lean proof composes
the corresponding Library reductions with the proved infinitesimal
character and Whittaker results.
