# Coordinate lattices in local coefficient spaces

Author: Worker 57.

## Construction and hypotheses

`basisLattice R b` is the actual submodule `span_R(range b)` of a vector
space `V` over a field `K`. Here `R` is a commutative domain acting through
an algebra structure on `K`, the scalar action on `K` is torsion-free, and
the actions on `V` form the indicated scalar tower. When the basis index
is finite, `basisLattice_isLattice` proves finite generation over `R` and
that the `K`-span is all of `V`. The construction depends on the chosen
basis; no basis-independent preferred lattice is asserted.

`mem_basisLattice` identifies membership with the condition that every
coordinate lies in the image of `R` in `K`. If `K` is a topological ring,
`V` carries its module topology, and the image of `R` is open, then
`basisLattice_isOpen` proves that this submodule is open. No compactness,
group action, or completeness hypothesis enters this coordinate argument.

For a number field `L`, a finite place `l` in the project's
`Langlands.Global.FinitePlace L` convention (a height-one prime of its
ring of integers), and a finite-dimensional `L`-vector space `W`, write
`K = FiniteCompletion L l` and `O = CoefficientIntegers l`. These are the
actual adic completion and its valuation subring. The completed
coefficient space is `K tensor_L W`.

`coefficientTopology L l W` supplies the module topology over `K` on that
space. `coefficientLattice L l W` takes the `O`-span of
`Module.finBasis K (K tensor_L W)`. The basis is chosen noncomputably;
its existence follows from finite-dimensional scalar extension. The
instance `coefficientLattice_isLattice` proves this is a full finitely
generated lattice. `coefficientLattice_isOpen` proves openness in the
explicitly supplied topology, using openness of the valuation subring
of the actual completion.

## Implemented arguments

Finite generation is `Submodule.fg_span` applied to the finite range of
the basis. Fullness follows from `Submodule.span_span_of_tower` and the
basis spanning theorem. The membership criterion is Mathlib's
`Module.Basis.mem_span_iff_repr_mem`. For openness, the set is the finite
intersection of the inverse images of `range(algebraMap R K)` under the
coordinate linear maps. Those maps are continuous by
`IsModuleTopology.continuous_of_linearMap`. In the local specialization,
the algebra-map image is definitionally the valuation subring, which is
open by `Valued.isOpen_valuationSubring`.

## Provenance and scope

This is a derived prerequisite for the coefficient constructions in
Harris--Taylor (2001), Section III.2, printed pages 94--95 (PDF pages
102--103), and Harris (1999), Section 3, printed pages 307--308 (PDF pages
9--10). Harris--Taylor starts from a continuous representation, passes to
a finite coefficient extension and an invariant finite free integral
lattice, and uses its reductions modulo rational-prime powers to construct
sheaves. Harris uses a level-stable integral lattice in the completed
coefficient space. Neither source states the coordinate construction here
verbatim. This module supplies an initial open full lattice, the input
required by the separately stated compact orbit-saturation construction.

The registered sources are:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

This module treats one completion `L_l`; it does not identify the full
product `L tensor_Q Q_ell`, prove stability of the chosen lattice, prove
continuity of an algebraic representation, establish openness of its
ideal-power submodules, descend a coefficient field, or construct the
associated sheaf. Those remain separate steps of the Harris specialization.
