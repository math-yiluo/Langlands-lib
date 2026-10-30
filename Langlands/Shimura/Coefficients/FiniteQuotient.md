# Congruence-group towers and finite quotient-ring coefficient actions

Author: Worker 57. Worker 1060 updated the orbit-continuity status paragraph
after the 2026-10-29 documentation audit (finding P3-040).

This module connects the published integral congruence kernels to the actions
over the actual quotient coefficient rings. It constructs their group tower,
proves compatibility with the coefficient transition maps, and specializes
the construction to the published orbit-saturated compact-level lattice.

## Group tower

For any commutative ring `R`, group `G`, ideal `I`, and actual action `M` on
an `R`-module, let `K_n` be the published `congruenceKernel I M n`, the kernel
of the action on `M / I^n M`. These are normal subgroups and decrease with `n`.
No finiteness or topology assumptions are needed in this general part.

`torsionCongruenceTransition I M h`, for `h : i ≤ j`, is the homomorphism
`G / K_j → G / K_i` induced by the identity of `G`. The formula on group
representatives is proved in `torsionCongruenceTransition_mk`; every such
transition is surjective. The identity and composition laws make
`torsionCongruenceGroups I M` a genuine functor from the opposite natural
number order to `GrpCat`. The proof of composition uses Mathlib's
`QuotientGroup.map_comp_map` with the two identity homomorphisms. It does
not expand the module quotient construction.

The generic ring, group and module carriers have independent universes.
The coefficient specialization below retains the common universe `u` of
the published coefficient interfaces.

## Quotient-ring actions

Let `Λ` be a published `StableCoefficientLattice` for the actual coefficient
place action of an algebraic representation. Its inputs are a finite-dimensional
rational algebra `A` with anti-involution, a number field `L`, an `L`-vector
space `W`, the representation of the scalar-extended similitude functor,
finite places `l` and `p` with `l` over `p`, and a subgroup `U` of the finite
adelic points. No continuity is required in this part. Finite generation is
available from the supplied lattice certificate; no extra finite-dimensionality
hypothesis on `W` is introduced here.

For a natural scalar `m`, `RationalCongruenceGroup m n` is precisely
`U / congruenceKernel (coefficientScalarIdeal l m) Λ.action n`.
The scalar ideal is `(m)` in the actual coefficient integer ring `O_l`.
It remains the rational scalar ideal at ramified places.

`rationalTorsionAction_ker` proves that the action over `O_l/(m)^n` has the
same kernel as the action on the same carrier viewed as an `O_l`-module.
Both implications compare linear maps pointwise; the underlying quotient
functions agree definitionally.

`rationalCongruenceAction m n` uses this equality to factor the actual
quotient-ring action through `RationalCongruenceGroup m n`.
`rationalCongruenceAction_mk` recovers the original reduced action on group
representatives. Together with the imported `rationalTorsionAction_mk`, this
computes the action on both group and coefficient representatives from the
original integral action. The new action is faithful: its homomorphism to the
endomorphisms of the module is injective, by Mathlib's kernel criterion for
an induced quotient homomorphism. Its underlying coefficient module is finite
for nonzero `m`, by the published finiteness theorem for the actual quotient
ring and the stable lattice. The imported quotient coefficient ring is finite
under the same hypothesis.

`rationalCongruenceTransition` and `rationalCongruenceGroups` specialize the
general group maps and functor. `rationalCongruenceTransition_equivariant`
proves that reducing coefficients from exponent `j` to `i` intertwines the
actions along `U/K_j → U/K_i`. The proof reduces first to a representative
in `U` and then to a lattice representative, where both sides are the same
quotient of the integral action. The coefficient map is the existing
surjective transition in `rationalTorsionSystem`, with scalars retained in
`O_l`: its source and target quotient coefficient rings differ. The statement
does not incorrectly place that map in a single quotient-ring module category.

All constructions allow exponent zero, and the finiteness conclusions allow
any nonzero natural scalar, including a unit. Neither primality nor a prescribed
residue characteristic for `m` is assumed.

## Constructed compact-level lattice

For finite-dimensional `W`, a compact open adelic level `U`, and the explicit
local orbit-continuity hypothesis `hρ` of `CompactCoefficient`,
`compactFiniteCoefficientAction` applies the preceding construction to
`compactStableCoefficientLattice`. This lattice is the span of the level's
translates of the actual coordinate lattice; it is not supplied as output data.

`compactFiniteCoefficientAction_finite` proves that both its congruence group
and coefficient module are finite for nonzero `m`. Group finiteness comes from
the published openness of the congruence kernel in the compact level; module
finiteness comes from `FiniteReduction`. The group transitions, faithfulness
and coefficient equivariance above apply to this same lattice.

This module retains `hρ` exactly, as an explicit hypothesis. The separate
algebraic orbit-continuity statement `AlgebraicOrbitContinuityStatement` is
proved by the published theorem `algebraicOrbitContinuity`. The published module
[AlgebraicCompactCoefficient](AlgebraicCompactCoefficient.md) supplies `hρ` as
`continuous_algebraicCoefficient_orbit ρ l`: its
`algebraicCompactCoefficientLattice` is `compactStableCoefficientLattice` with
that argument, and `algebraicCompactFiniteCoefficientAction` and
`algebraicCompactFiniteCoefficientAction_finite` give the corresponding finite
quotient-ring actions and their finiteness without a continuity hypothesis.

This module does not identify these congruence quotients with geometric deck
groups, construct a tower of scheme covers, or prove local triviality of an
associated sheaf. It also asserts neither that the intersection
of all kernels is trivial nor that the original level equals the inverse limit.

## Derived provenance

The construction is derived from the published modules
[CompactCoefficient](CompactCoefficient.md), [FiniteReduction](FiniteReduction.md)
and their integral congruence-kernel infrastructure. The intrinsic group laws
are proved using Mathlib's quotient group maps; the scalar and module
constructions use the published actual coefficient ring and module quotients.

Its source motivation is Harris (1999), *Galois properties of cohomological
automorphic forms on GL(n)*, Section 3, printed pp.307–308 (PDF pp.9–10),
registered source `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
That passage uses a stable lattice and finite torsion coefficients whose
continuous action factors through a finite congruence quotient. Harris's chosen
congruence filtration is not asserted to equal the coefficient-kernel tower
constructed here.

Harris–Taylor (2001), *The Geometry and Cohomology of Some Simple Shimura
Varieties*, Section III.2, printed pp.94–95 (PDF pp.102–103), registered source
`harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
uses an invariant finite free integral lattice, its rational-prime-power
reductions, finite deck-group factorization and compatible coefficient maps.
The present general group tower and faithful quotient-ring actions are
algebraic prerequisites for that use, not a claimed construction of the
geometric covers or their comparison isomorphisms.
