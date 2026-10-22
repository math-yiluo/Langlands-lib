# Compact stable lattices and open congruence kernels

Author: Worker 57.

This module states two topological prerequisites for the integral coefficient
construction in `Langlands.Shimura.Coefficients.Lattice`. The declarations are
proposition-valued definitions, not assertions that the propositions have been
proved. `LatticeTopologyStatement` is their conjunction and is the proof target.

## Compact orbit saturation

`CompactLatticeStatement` quantifies over a commutative ring `R`, a commutative
`R`-algebra `K`, and a `K`-module `V` with a compatible `R`-module structure.
The additive group of `V` is topological. It also quantifies over a group `G`
with a compact topology and a homomorphism `rho : G ->* (V ≃ₗ[K] V)`.
Every orbit map `g ↦ rho(g)x` is required to be continuous. No topology on `R`
or `K`, and no continuity of multiplication on `G`, is needed in this clause.

For every full `R`-lattice `Lambda` in `V` that is open in `V`, the conclusion
is that the actual `orbitSpan rho Lambda` is a full lattice, is stable under
`rho`, and is open. A full lattice means finite generation over `R` and full
`K`-span, as in Mathlib's `Submodule.IsLattice`. The initial lattice need not
already be stable. In particular, this statement gives a specific stable
lattice containing it, rather than just the existence of some unspecified
submodule. Neither a noetherian coefficient ring nor a field assumption on
`K` is imposed.

The open initial lattice is a real hypothesis. This declaration does not
construct such a lattice in a topological vector space. For a local coefficient
space this step requires a coordinate lattice and a proof that it is open.

## Congruence kernels

`CongruenceKernelTopologyStatement` quantifies over a commutative ring `R`,
a compact group `G` with separately continuous multiplication, and a module
action `M : Action (ModuleCat R) G`. The carrier of `M` is a finite `R`-module
in the algebraic sense of finite generation; it is not assumed to be a finite
set. Its additive group is topological, and all orbit maps are continuous.

For an ideal `I` and natural number `n`, the submodule `I^n M` must be open
in `M`. The conclusion is that `congruenceKernel I M n` is open in `G` and
that `G / congruenceKernel I M n` is a finite set. The kernel is exactly the
kernel of the already constructed action on `M / I^n M`; its normality and
the action on the quotient group are supplied by `Lattice`. Thus this
conclusion supplies a finite group for that existing factorization. It makes
no assertion that a specified finite cover realizes that group.

At index zero, the reduction is the zero module and the kernel is all of `G`.
The statement does not require finiteness of `R/I^n`: compactness of `G` and
openness of the kernel suffice for the group quotient's finiteness. Finiteness
of the coefficient carrier itself is a separate theorem in `Lattice` with
its own hypotheses.

## Original sources and derived scope

Worker 57 reread Harris--Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.2, printed pp.94--95 (PDF pp.102--103). Page 94
starts with a continuous representation of the inverse limit of finite deck
groups, passes to a finite coefficient extension and an invariant finite free
integral lattice, and factors each reduction through a finite deck group.
Page 95 uses compatible maps of the reductions in constructing morphisms of
coefficient sheaves.

Worker 57 also reread Harris, *Galois properties of cohomological automorphic
forms on GL(n)* (1999), Section 3, printed pp.307--308 (PDF pp.9--10). The
passage chooses a stable integral lattice and then uses continuous torsion
coefficients whose action factors through a congruence quotient.

These two propositions are derived topological prerequisites for those
passages, not transcriptions of an expressly numbered theorem there. Compact
orbit saturation can be proved by covering each compact orbit of a finite
set of generators by finitely many cosets of the open lattice. The kernel
can be tested on finitely many module generators; its equations are open
conditions when `I^n M` is open. These observations explain the explicit
hypotheses and the generality beyond local fields.

The declarations do not address descent of a representation from an algebraic
closure to a finite coefficient field, the Baire-category argument in
Harris--Taylor, continuity of the particular algebraic `placeAction`, the
construction of an open local coordinate lattice, openness of its ideal
powers, or realizing a finite quotient by a level of a geometric tower.
Those steps remain requirements for the Harris specialization. The rational
prime ideal `(ell)` remains the intended ideal for Harris's reductions; no
identification with a uniformizer ideal is made at ramified places. No local
system, sheaf descent, or scheme model is claimed here.

Sources:

- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies are `Coefficients.Lattice` and Mathlib's compactness and
open-subgroup libraries, at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
