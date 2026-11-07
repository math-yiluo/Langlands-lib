# Signed composition and cosets of actual witnesses

Worker 1813 authored this internal algebraic companion to
`DeligneHenniartWitnessAlgebra`. It retains the published signed actual Weil
lattice, supplied assignment, reciprocity family, additive character, Haar
measures, exact tensor and determinant. Its only additional hypothesis on the
assignment is its existing additivity relation.

`pPowerTorsion p A` is the additive subgroup of an arbitrary commutative group
consisting of elements annihilated by some `p^n`. To add elements annihilated
by `p^m` and `p^n`, the proof uses `p^(m+n)` as a common annihilator.
Negation preserves an exponent. No exponent uniform across elements is
asserted, and this construction does not require primality.

`witnessRatio` is an additive homomorphism on pairs consisting of a signed
lattice and the additive type tag of a field unit. It subtracts the additive
tag of determinant evaluation from that of epsilon evaluation on the tensor
with a fixed test lattice. The type tag changes notation only: subtraction
is the ratio of the actual complex units, with no logarithm selected.
The two ratio lemmas identify zero with the exact equality and membership
in `pPowerTorsion` with the required equality of `p^n`-th powers.

`exactWitnessGroup` and `approximateWitnessGroup` quantify these conditions
over all dimension-zero tests satisfying the appropriate strict break bound
and every Haar measure. Their subgroup proofs use additivity of the ratio
and the subgroup laws for zero or p-power torsion. The membership equivalences
use the proved lift-free witness equivalences; thus they describe the original
universal-lift definitions, including the dependence of each approximate
exponent on its test and measure.

The composition lemmas prove that witnesses multiply when signed lattice
inputs add, invert when those inputs negate, and take integer powers for
integer multiples of the input. These hold at any fixed real break bound,
without imposing a support condition on either input or its sum.

The two coset lemmas show that, given a witness `gamma` for `v`, another unit
`gamma'` is a witness exactly when `gamma' / gamma` is a witness for the zero
input. They follow by adding the inverse pair, and conversely adding the
given pair. This is a coset description by the determinant annihilator.
It does not identify that annihilator with a principal-unit subgroup, produce
a witness, or assert its valuation. Those are separate arithmetic obligations
of the unchanged `VirtualStabilityStatement`.

These are derived results from the published witness definitions, determinant
character laws and exact tensor bilinearity, rather than new source assertions.
The Markdown describes the implemented subgroup proof.
