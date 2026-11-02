# Full Harris coefficient diagrams on original CM kernel levels

Author: Worker 57.

This module constructs the inverse diagram of the actual small CM coefficient
levels, their original residual quotient groups, and the full Harris coefficient
reductions equivariant for those groups. The coefficient and group transitions
are surjective. It specializes the published torsion system and CM normal
refinement maps without changing their inverse-unop convention.

The arithmetic data are the universe-zero central-simple unitary data
`D : CentralSimpleUnitaryData E F A d`, with E totally real, F totally
complex and quadratic over E, the indicated E-, F- and rational algebra
structures on A, and the rational scalar tower and finiteness hypotheses
needed by the coefficient constructors. The surrounding declarations also
carry the CM and compatible scalar-tower instances used by the existing CM
interfaces. The coefficient field K is a number field, W is a finite
K-module, rho is an algebraic representation of
`D.rationalInvolution.baseChange K` on W, p is an actual rational finite
place, and U is an actual `SmallCMLevel D`.

Write Uord for `CompactOpenLevel.inverseOpposite U.obj` and e for
`CompactOpenLevel.inverseOppositeEquiv U.obj`. Thus e sends an element of
the opposite CM level group to its inverse-unop in the ordinary level
group. Put R = `HarrisCoefficientIntegers K p`, the full product of the
integral coefficient rings at all places over p, and J =
`harrisCoefficientScalarIdeal K p m`. Let Lambda be the stable full Harris
lattice with its published ordinary-level action.

`cmHarrisTorsionSystem` composes `harrisTorsionSystem` with action
restriction along e. Its kth module is Lambda modulo J^k Lambda, retaining
R as its scalar ring so that different exponents lie in one module
category. The formula `cmHarrisTorsionSystem_obj_carrier` identifies its
carrier with that of the published full quotient-ring action
`cmHarrisFiniteTorsionAction`. The theorem `cmHarrisTorsionSystem_ker`
identifies its action kernel with `cmHarrisCongruenceKernel`. Its proof
unfolds action restriction and the published kernel comparison, so both
sides are the kernel of the same composite homomorphism. These two
statements concern the carrier and kernel; they do not assert equality
between objects in different module categories.

`cmHarrisCongruenceKernel_antitone` proves that the actual CM kernels
decrease with the exponent. It applies the published congruence-kernel
antitonicity and subgroup inverse-image monotonicity along e.
`cmHarrisCoefficientLevel_antitone` then applies ambient subgroup-image
monotonicity to the actual levels inside the finite-adelic CM group.
The torsion-system and kernel assertions allow any natural m. The
compact-open level constructions below require m nonzero; exponents are
arbitrary natural numbers, including zero.

Let V_k be `cmHarrisCoefficientLevel D rho p U m hm k`, the already
constructed small normal level cut out by the full coefficient kernel.
`cmHarrisCoefficientLevels` is an actual functor from the opposite
natural-number category to `SmallCMLevel D`, with object V_k and maps
the identity-element inclusions obtained from antitonicity. Its identity
and composition laws use `smallCMInclusion_refl` and
`smallCMInclusion_trans`. `cmHarrisCoefficientLevelProjection` is the
natural transformation to the constant diagram at U, with the existing
inclusion V_k into U at every index. Naturality follows from the same
composition law. Compactness, openness, smallness and relative normality
are inherited from the proved coefficient-level construction.

`cmHarrisCoefficientGroups` has kth object
`SmallCMResidualGroup D U V_k`, namely U modulo the subgroup of V_k
inside U. Its maps are precisely `smallCMResidualQuotientMap` for the
proved inclusions of the actual V_k. The imported normality instance
supplies quotient group structures. Identity and composition follow
from the existing residual-map laws. The theorem
`cmHarrisCoefficientGroups_map_mk` says that every map sends the class
of g in U to the class of the same g. The theorem
`cmHarrisCoefficientGroups_map_surjective` specializes the proved
surjectivity of these quotient maps, and
`cmHarrisCoefficientGroups_finite` specializes the proved finite-index
result for small CM levels.

`cmHarrisCoefficientDiagram` is an `EquivariantDiagram` over this exact
group functor with values in `ModuleCat R`. Its underlying functor is
the transported torsion system with its U-action forgotten. At k its
action is the quotient lift of that integral action through the actual
subgroup of V_k in U. Containment in the action kernel follows from
`cmHarrisTorsionSystem_ker` and the published equality
`cmHarrisCoefficientLevel_subgroupOf`; no additional containment premise
is supplied. Transition equivariance is proved by induction on a
residual-group representative, reducing to equivariance of the original
torsion-system map.

`cmHarrisCoefficientDiagram_obj` identifies the entire underlying functor.
`cmHarrisCoefficientDiagram_obj_carrier` identifies each carrier with
that of the published `cmHarrisCoefficientAction` over R/J^k.
`cmHarrisCoefficientDiagram_action` proves agreement of those two
actions on every residual element and coefficient value, by quotient
induction. `cmHarrisCoefficientDiagram_action_mk` gives the explicit
representative formula: the class of g acts on the class of x by taking
the class of the original lattice action of e(g) on x.

`cmHarrisCoefficientDiagram_transition_mk` identifies every coefficient
transition with the quotient map keeping the same lattice
representative. `cmHarrisCoefficientDiagram_transition_surjective`
reuses surjectivity of the full Harris torsion-system maps.
`cmHarrisCoefficientDiagram_finite` reuses finiteness of the full
Harris reductions. Thus the module carriers and residual groups are
finite for nonzero m. The construction does not assert freeness over
R/J^k or triviality of the intersection of the kernels.

The source motivation is Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, Section 3, printed pp.306–308,
one-based PDF pp.8–10: algebraic coefficient representations over number
fields, stable integral lattices and the inverse function-equivariance
in (3.7), followed by normal congruence subgroups and finite quotient
factorization before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
Harris's additional hypotheses for his chosen congruence sequence and
free finite coefficients are not asserted for this internal sequence.

Harris–Taylor (2001), *The Geometry and Cohomology of Some Simple
Shimura Varieties*, III.1, printed pp.90–91, one-based PDF pp.98–99,
gives small levels, right frame composition and normal U/V covers.
III.2, printed pp.94–95, one-based PDF pp.102–103, motivates compatible
torsion coefficients on varying finite covers and their
inverse-equivariant function description. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The exact inverse-unop transport, actual kernel sequence and categorical
diagram here are internal deductions from the published constructions.
The use of any nonzero natural scalar and nonnegative exponent is a
documented extension of the reduction parameters in the motivating
passages. This module supplies arithmetic level indices, group maps
and coefficient maps. Scheme representability, the original scheme
tower and its deck maps, associated sheaf transitions, comparison
with the source's function description or a different representation
normalization, independence of choices and the full lisse adic
construction remain separate obligations.
