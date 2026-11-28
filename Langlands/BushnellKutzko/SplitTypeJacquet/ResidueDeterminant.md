# Residue determinants on the simple-stratum groups

`IsRelativeResidueDeterminant` specifies the determinant used on the
relative units \(U(\mathfrak B)\). It asks for a multiplicative equivalence
from the units of the residue field of \(E=F[\beta]\) to the codomain of a
given homomorphism. For each relative unit, its \(E\)-linear determinant
must lift to an integral unit whose residue, under that equivalence, gives
the value of the homomorphism.

`IsRelativeResidueDeterminant.comp_inclusion` restricts the condition to
a subgroup of relative units with the same parameter. It keeps the residue
unit equivalence and the individual determinant lifts.
`IsRelativeResidueDeterminant.comp_parameterCongr` transports the condition
along equality of the parameters by substitution.

`IsSimpleJResidueDeterminant` requires the supplied homomorphism on
\(J(\beta,\mathfrak A)\) to be trivial on \(J^1(\beta,\mathfrak A)\) and to
satisfy the relative residue determinant condition on \(U(\mathfrak B)\).
These conditions express the determinant in the classification by character
twists in Bushnell and Kutzko (1993), (5.2.2)(ii), printed p. 166 (PDF p. 178).
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
