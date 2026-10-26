# The congruence coefficient diagram over its varying groups

Author: Worker 13.

This internal construction assembles published quotient actions and quotient
maps into an `EquivariantDiagram`. For a commutative ring `R`, a group `G`,
an `R`-module representation `M`, and an ideal `I`, the group diagram is
`torsionCongruenceGroups I M` from
[FiniteQuotient](FiniteQuotient.md). Its term at `n` is `G / K_n`, where
`K_n = congruenceKernel I M n` is the kernel of the action on `M / I^n M`.

The underlying module diagram of `congruenceCoefficientDiagram I M` is
exactly the published `torsionSystem I M` followed by the action forgetful
functor. The action at each index is the published `quotientTorsionAction`
with normal subgroup `K_n`. Its kernel inclusion is reflexivity, so no
additional factorization hypothesis is needed.

For an inverse-index arrow from `j` to `i`, the group map is the
identity-induced quotient map `G / K_j → G / K_i`, and the module map is
the actual reduction `M / I^j M → M / I^i M`. Their equivariance is proved
by induction on a representative of the source quotient group and the
existing equivariance of `torsionSystem`. Thus the group and module
diagrams form one coherent object; no transition map is supplied as
an unspecified function.

The action and underlying-transition formulas are definitional equalities.
Every coefficient transition is surjective by the published surjectivity
theorem for ideal-power module quotients. Exponent zero is included.
The ring, module carrier, and original group have independent universes.
No topology, finite generation, or finiteness assumption is required.

The generic construction applies in particular to the published
`StableCoefficientLattice.action` and its ideal of a rational scalar.
This is an algebraic input for the Harris coefficient construction. It
uses integral `R`-linear transition maps because the quotient coefficient
rings can differ at different indices. It constructs neither geometric
covers nor inverse maps between their associated sheaves. Those inverse
maps require the separately stated geometric torsor comparison theorem.
Tensor comparison, reduction of sheaves, and actual Harris specialization
remain separate obligations.

The provenance is the direct combination of
[EquivariantDiagram](../../CategoryTheory/EquivariantDiagram.md),
[Lattice](Lattice.md), and [FiniteQuotient](FiniteQuotient.md). No new
claim is attributed to external literature.
