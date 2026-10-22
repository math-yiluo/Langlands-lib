# Actual twists of the supercuspidal lattice

This is a derived integral extension of the published supercuspidal class twist,
using the actual classes and rank conventions of `Supercuspidal.Basic`.
The field and representation-carrier universes are independent. Carriers may be
infinite dimensional. Degree means the rank of the general linear group,
extended integrally; it is not the dimension of the representation carrier.

For each positive rank the construction takes a complex-unit character of the
actual general linear group, an open-kernel proof, and a proof that the character
is trivial on the determinant kernel. The imported class construction proves
preservation of smoothness, admissibility, irreducibility and supercuspidality.
It twists the action on its original carrier and descends actual isomorphisms.
`twistClassEquiv` uses the inverse character for the inverse map; the two kernels
are equal. The imported composition and identity laws prove both inverse laws.
No representative is chosen to define the quotient operation.

`twistBasisEquiv` applies these equivalences in each positive rank and retains the
rank label. It commutes with the underlying smooth dual class and agrees with
the actual object twist on basis classes. `twistLatticeEquiv` is finite-support
reindexing over the integers. Its generator and coefficient formulas follow
from that reindexing. Linear induction proves degree and coefficient-pairing
preservation; bijectivity proves preservation and reflection of effectiveness.
The identity, product and inverse laws hold on both bases and lattices. The
product law explicitly requires openness of the product kernel in this general
topological-field interface.

For an actual p-adic field, `realPowerTwistBasisEquiv` and
`realPowerTwistLatticeEquiv` specialize these constructions to the canonical
topology and to the published character `g ↦ |det g|^s`. Its absolute value is
the actual residue-normalized one; the open-kernel and determinant-kernel proofs
are supplied by the published local-field constructions. Rank, generators,
coefficients, degree, pairing and effectiveness specialize accordingly. The
zero exponent is the identity, composition adds exponents, and the inverse
negates the exponent, on both bases and lattices. These follow from the
published real-power character laws and the preceding twist laws.

This module supplies no unitary restriction, smooth contragredient operation,
finite orbit count, induced/global-image spanning, or cross-side isometry. In
particular, general real-power twists need not preserve unitarizability. The
pairing here is the concrete integral coefficient pairing.

The motivating source is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Inventiones mathematicae 139 (2000),
439–455: section 1.1 (p.439) specifies supercuspidal classes; section 1.2(2) (p.440) specifies scalar twisting; sections
2.5–2.6 (pp.446–447) use the integral extension and the orthonormal basis pairing.
The rank-wise equivalences and reindexing laws here are internal derived
constructions, not an assertion of Henniart's global comparison theorem.
