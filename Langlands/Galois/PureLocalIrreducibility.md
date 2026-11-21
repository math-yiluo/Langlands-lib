# Absolute irreducibility from a weakly associated family

`PureLocalIrreducibilityTransferStatement` considers two pure compatible
families of possibly different weights that are weakly associated to the same
numerical spectrum. The chosen members have equal positive rank. Their
coefficient completions embed continuously into a common Hausdorff
algebraically closed field with a complex identification compatible with both
coefficient embeddings. If the first local restriction becomes irreducible
over this common field, the second restriction is absolutely irreducible
over its own coefficient completion.

This is an internal consequence of the Library's weight parity, arithmetic
Euler polynomial comparison, and one-sided irreducible character comparison.
`pureLocalIrreducibilityTransfer` takes an integral half-weight difference
from parity and compares the first family with the corresponding inverse
cyclotomic twist of the second. Equality of the mapped Euler polynomials
away from finitely many places gives an actual equivalence of the
scalar-extended restrictions. In particular the extended twist is
irreducible.

After local restriction and scalar extension, the twisted action multiplies
the untwisted action by the image of the restricted unit character. The
twist preserves the ordered lattice of invariant subspaces.
`Langlands.isIrreducible_twist_iff` therefore gives irreducibility of the
untwisted scalar extension. The Library's scalar-extension theorem then
gives irreducibility over the algebraic closure of the second coefficient
completion. Applied to an irreducible cohomological witness, this gives
irreducibility for other pure weakly associated families in the
split-supercuspidal comparison.
