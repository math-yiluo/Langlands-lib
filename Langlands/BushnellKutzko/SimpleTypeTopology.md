# Topology of the unit groups used in simple types

`generalLinearToLinContinuous` equips Mathlib's
`Matrix.GeneralLinearGroup.toLin` with a homeomorphism. The topology on
\(\operatorname{End}_F(F^n)\) is the module topology over \(F\). The linear
maps between the endomorphism algebra and the matrix algebra are continuous
in both directions, and the equivalence passes to their groups of units.

Each endomorphism filtration step of a lattice chain is a finite
\(\mathfrak o_F\)-module that spans the endomorphism algebra over \(F\).
The proof of spanning clears a power of a uniformizer. Extending an
integral basis to an \(F\)-basis identifies this step with a product of
copies of \(\mathfrak o_F\), so it is compact and open. The conditions
for membership in \(U^k(\mathfrak A)\) are open conditions on a unit,
its inverse and its difference from the identity. Compactness of
\(U^0(\mathfrak A)\) follows by taking the units of the compact order.
The recursion for \(\mathfrak J(\beta,\mathfrak A)\) contains a sufficiently
deep endomorphism filtration step and the identity. For each \(i\geq 0\),
`isCompact_isOpen_simpleJGroup` uses a depth at least \(i\) to exhibit an
open filtration subgroup inside \(J^i\). Each \(J^i\) is closed by openness
and lies in the compact \(U^0(\mathfrak A)\). `simpleJOpenSubgroup` equips
the same subgroup with its openness proof for restriction of representations.
The theorem for `simpleJ` takes \(i=0\).

These are topological properties of the groups used in Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
§1.1, printed pp. 19–22, (3.1.8) and (3.1.14), printed pp. 90–91 and 95,
and (5.5.10), printed pp. 184–185.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
