# Imaginary parameters and actual imaginary periods

This construction realizes the imaginary parameter group and its period
subgroup in Renard 2026 V.3.20, printed p.116/PDF p.122. It uses the
published actual rational-character valuation image and the existing real
and complex additive duals. Worker 6 authored this unit.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definitions and short intrinsic laws are an internal realization of
the source's `i a*` and its stated period subgroup; this is not a proof of
the compact-torus assertion at the end of that passage.

Write `Lambda = Additive (rationalDiscreteValuationImage G)`,
`V = Hom_Z(Lambda,C)` and `L = log q`, where `q` is the residue
cardinality. The exponential convention remains `exp(-lambda(a)*L)`.

`rationalImageImaginaryParameters G` is the additive subgroup of `V`
consisting of functionals whose value at every actual image element has
zero real part. Its membership is equivalent to vanishing of the
published `rationalImageParameterRealPart`. The additive equivalence
`rationalImageImaginaryParameterEquiv` identifies the actual real dual
with this subgroup by `phi -> i*phi`; its inverse takes the imaginary part
pointwise. The inverse laws follow by equality of real and imaginary
parts, and the additive law follows from distributivity.

The existing period subgroup is
`P = (2*pi*i/L) Hom_Z(Lambda,Z)`, defined as an actual homomorphism range.
`rationalImagePeriodLattice_le_imaginary` proves directly that every such
period has zero real part. This uses the displayed scalar formula, without
an exponential-kernel assertion or a finite-rank premise.
`rationalImageImaginaryPeriodLattice` is the inverse image of `P` under
the subgroup inclusion. Its membership law and its image equality show
that these are precisely the same periods inside the imaginary group;
no replacement lattice is chosen.

`rationalImageImaginaryCharacter` restricts the existing exponential to
the imaginary parameter group and restricts its codomain to the existing
norm-one subgroup of complex characters. Its norm-one proof is the
published exponential norm formula with zero real part. Its underlying
character is definitionally the original complex exponential.

With `rationalImageComplexParameterTopology G` installed locally, the
imaginary parameter group has the inherited subgroup topology. Continuity
of this restricted exponential follows from continuity of the original
exponential and the two subtype maps. Character spaces retain their
existing compact-open subgroup topologies.

For an affine group scheme locally of finite type,
`rationalCanonicalImaginaryUnramifiedCharacter` composes the restricted
exponential with the existing unitary image-to-unramified multiplicative
homeomorphism for the canonical rational-point topology. Its value at
each actual point is exactly
`exp(-lambda(H_G(g))*L)`. Connected reductivity supplies these geometric
assumptions in later applications.

There is no additional splitting, characteristic-zero, finite-rank or
special linear-group premise. These constructions do not prove that
periods are discrete or closed, that the imaginary quotient is compact,
or that the restricted exponentials are open quotient maps inducing the
prescribed quotient homeomorphisms. Those are separate statements and
proof obligations. The tensor, split-center, pure-tensor norm formula and
algebraic-torus comparisons also remain separate.
