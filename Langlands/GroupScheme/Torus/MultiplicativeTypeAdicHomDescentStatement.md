# Diagonalizable adic Hom comparison and finite étale descent

These propositions separate the two mathematical parts of SGA 3, Exposé IX,
Théorème 7.1 (Gille–Polo recomposed edition, 2009, pp.56–59, original margins
pp.68–72), registered source `sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The separation is an internal organization of its proof.

`Langlands.GroupScheme.DiagonalizableAdicHomComparisonStatement` is the
globally diagonalizable case. For a noetherian commutative ring `A`, an ideal
`I` with `IsAdicComplete I A`, and group schemes `H`, `G` over `Spec A`,
assume `H` is diagonalizable and `G` is affine over `Spec A`. Restriction
from actual global homomorphisms to compatible homomorphisms on all
`Spec(A/I^(n+1))` is bijective. The system and restriction map are the
existing `HomScheme.Adic.System` and `System.restrict`. The statement
requires no smoothness, flatness, or finite-type hypothesis on `G`.

`Langlands.GroupScheme.MultiplicativeTypeAdicHomDescentStatement` says that
this diagonalizable comparison, for every ring and ideal in the given
universe, implies the full
`Langlands.GroupScheme.MultiplicativeTypeAdicHomComparisonStatement` in that
universe. The full statement replaces global diagonalizability by
diagonalizability after some finite étale surjective cover. All other
hypotheses and the actual restriction map are unchanged.

The source's descent argument begins with the finite étale splitting cover,
uses adic completeness of its finite coordinate algebra and of the double
overlap, applies the diagonalizable comparison there, and uses the
equalizer description of homomorphisms to descend. The present implication
retains this descent as a proof obligation; it assumes the globally
diagonalizable comparison and does not assume either completeness
transport or Hom descent as additional hypotheses. The file states these
propositions and provides no proof of either.
