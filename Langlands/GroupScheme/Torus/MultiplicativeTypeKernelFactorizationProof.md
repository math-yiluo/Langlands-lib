# Canonical factorization of homomorphisms from groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeKernelFactorization` proves
`MultiplicativeTypeKernelFactorizationStatement` in every universe. The
statement applies over any scheme \(S\) to a homomorphism \(f : H \to G\)
with \(H\) of multiplicative type and \(G\) separated over \(S\), when \(S\)
is locally noetherian or \(G \to S\) is finitely presented.

The proof applies the published factorization reduction to the published
central-rigidity and monomorphism-spreading theorems. The reduction uses
the local triviality clause of central rigidity (IX, Corollaire 5.2) and
the local monomorphism clause for separated targets (IX, Corollaire 6.6).
[Factorization reduction](MultiplicativeTypeKernelFactorizationReduction.md),
[central rigidity](MultiplicativeTypeCentralRigidityProof.md),
[monomorphism spreading](MultiplicativeTypeMonomorphismSpreadingProof.md).

On an fppf diagonalizing cover, at each base point the reduction extends
the residue-field kernel to a diagonalizable closed subgroup of the split
source by using its quotient character group. Local triviality shrinks the
base to a neighbourhood where \(f\) kills that subgroup and factors through
its quotient. The induced map on the quotient is monic over the chosen
residue field. Monomorphism spreading gives a smaller neighbourhood
where it is monic, so the extended subgroup is the actual kernel there.
Kernel base change and fppf locality give multiplicative type of the
kernel over \(S\). In the locally noetherian case the diagonalizing cover
has locally noetherian sources by local finite presentation.
[Kernel reduction](MultiplicativeTypeKernelRigidityReduction.md).

The factorization construction then takes the relative quotient by the
full kernel. It has multiplicative type, and its projection is affine
and fppf with the prescribed kernel. Fpqc descent produces the homomorphism
to \(G\), and the full-kernel criterion makes it monic. The composition
with the quotient projection is \(f\).
[Factorization from the kernel criterion](MultiplicativeTypeFactorizationFromKernel.md).

This implements SGA 3, Exposé IX, Théorème 6.8, pp. 55–56 (original
margins 67–68) in the Gille–Polo recomposed edition of 8 November 2009,
registered as `sga3-expose-ix-gille-polo-2009` (SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`).
