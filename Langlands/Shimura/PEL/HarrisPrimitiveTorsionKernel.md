# Finite kernels of the normalized Harris polarization

Fix the arithmetic and signature data of `HarrisPrimitiveSourceForm`.
For a source map \(u\) and natural numbers \(a,m\), `HarrisPrimitiveSourceTorsionKernel`
is the subtype of the fixed source modulo \(m\) consisting of
residue classes that have a representative \(v\) such that every
value of the \(a\)-multiple of the primitive source form against
\(u(v)\) is divisible by \(m\) in the integral finite adeles.

Take a polarized Harris abelian scheme over a connected, locally
noetherian, quasi-separated base on which every positive integer
is a unit. At an algebraically closed point of characteristic zero,
assume a normalized Weil frame and a primitive homomorphism \(\mu\)
in the original polarization ray. With the named transition,
duality and torsion hypotheses, for \(m>0\),
`primitivePolarization_levelMap_mkQ_eq_zero_iff` identifies the
source divisibility condition with vanishing of \(a\mu\) on the
corresponding geometric \(m\)-torsion vector. The actual integral
Weil values come from the fixed source values multiplied by an
integral unit using `harrisPrimitiveWeilUnit_integralAlong_nsmul`.
Multiplying by that unit keeps exactly the same divisibility
condition. If the \(m\)-torsion image vanishes, the full dual Tate
vector is an \(m\)-multiple by `full_exists_nsmul_of_evaluation_eq_zero`,
which makes every integral pairing value an \(m\)-multiple.
The converse uses `integralWeil_exists_nsmul_of_forall`.
If an actual endomorphism \(f\) acts via \(u\) in the normalized full
integral frame, `Tate.evaluation_map` transports this relation to torsion
and `AbelianScheme.Tate.levelMap_comp` transports it to \(f \gg a\mu\).
`primitivePolarizationLevelKernelEquiv` then restricts
`harrisIntegralFrameTorsionEquiv` to its kernel.

If \(f \gg a\mu\) is an isogeny and \(m\) kills all its geometric kernel
points, `primitivePolarization_nativeRank_eq_card_sourceKernel`
computes the original native rank at every point of this geometric
fibre as the cardinality of the fixed source kernel. The kernel of
the level map includes every point of the actual isogeny kernel
at such an annihilating level. The rank comparison uses
`finrank_eq_card_fullIsogenyCokernel_at` and `fullIsogenyCokernelEquiv`.
For two such objects, possibly over different bases and geometric
point fields, the product of the orders of the finite geometric
kernels kills both. Applying the formula at this common level gives
`primitivePolarizationComp_nativeRank_eq` for the same \(u\) and \(a\).
`primitivePolarization_nativeRank_eq` specializes to the identity
endomorphisms and identity source map.

These are derived degree comparisons for the fixed normalized
Harris lattice and the actual abelian-scheme Weil pairing.
