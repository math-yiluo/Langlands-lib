# Continuous coefficient-place point maps

Author: Worker 57.

## Construction and hypotheses

Let `A` be a rational algebra with rational-linear anti-involution `σ`.
For a field `L` over the rationals and a commutative ring `S` with rational
and `L`-algebra structures, the published `towerMap L S` sends
`s ⊗ a` to `s ⊗ (1 ⊗ a)`. Give both tensor products their `S`-module
topologies. `continuous_towerMap` proves this map continuous.
`continuous_towerPoints` proves continuity of the induced map from
`σ.Points S` to `(σ.baseChange L).Points S`, for their published topologies
inherited from units, products and subgroups. These two results need a
topology on `S`, and do not require finite-dimensionality of `A`.

Now suppose `A` is finite-dimensional over the rationals, `L` is a number
field, `p` is a finite place of the rationals and `l` is a finite place of
`L` lying over `p`. The definition `coefficientPlaceMap σ p l` is the
continuous group homomorphism

`σ.FiniteAdelicPoints → (σ.baseChange L).Points (FiniteCompletion L l)`.

Its underlying homomorphism is the composition of three already constructed
maps: evaluation at `p`, extension from the rational completion to the
completion at `l`, and the tensor-tower point map. The middle map uses the
actual completion embedding `FiniteExtension.completionMap p l`.
No additional continuity hypothesis is attached to this homomorphism.

For an `L`-module `W` and an algebraic representation `ρ` of `σ.baseChange L`,
`placeAction_eq_comp_coefficientPlaceMap` identifies the published
`ρ.placeAction p l` with `ρ.act (FiniteCompletion L l)` composed with this
homomorphism. `continuous_placeAction_orbit` then proves continuity of every
finite adelic orbit map **assuming** continuity of every orbit map of this
completed algebraic action. Both the hypothesis and conclusion explicitly
use the completion-module topology on `FiniteCompletion L l ⊗[L] W`.
This reduction does not require `W` to be finite-dimensional.

## Implemented argument

The tensor-tower map is `S`-linear, so the universal property of the module
topology proves it continuous. Continuity on units, products and subgroup
inclusions gives the point-map result. The completion extension and finite
adelic evaluation have published continuity proofs. Their composition with
the tower point map supplies the required continuous homomorphism.

The action comparison is definitional: the published `placeAction`,
`finiteAdelicVia` and `actVia` have precisely this composite as their point
map. Composition of continuous functions proves the conditional orbit-map
result.

## Provenance and scope

This is derived topological infrastructure for the following original sources:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), Section 3, printed pp.307–308 (PDF pp.9–10), registered as
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
  The stable integral lattice and continuous torsion actions motivate
  proving continuity for the adelic coefficient action.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), Section III.2, printed pp.94–95 (PDF pp.102–103),
  registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  This passage uses a continuous inverse-limit deck action and integral
  reductions factoring through finite deck groups.

Neither source states the general tensor-topology lemmas verbatim. The
present construction isolates the continuous map of groups needed to connect
the published algebraic representation to the local coefficient topology.
It treats one completion `L_l`; it does not identify Harris's
`L ⊗_ℚ ℚ_p` with its product of local factors.

Continuity of an arbitrary algebraic representation remains an explicit
unproved prerequisite here. The module also does not construct a stable
lattice, prove a finite deck-group factorization, or descend a coefficient
sheaf on Shimura scheme levels.
