# Realizing finite local invariant values in idele cohomology

Author: Worker 21.

This internal construction concerns a Galois extension `E/F` of number fields
in an arbitrary common universe. It uses the supplied local invariant family
`I`; only its `RelativeImages` laws are required.

`finiteIdeleInvariantLift I hI v w` maps the denominator subgroup of order
`[E_w:F_v]` additively into actual `H²(Gal(E/F), J_E)`. It first applies the
inverse of `relativeInvariantEquiv` for the supplied invariant and then the
published `ideleLocalSection`. As in that section, the interface takes a
`Fintype` instance on the quotient by the decomposition subgroup.

The invariant at `w` of the lifted class is the original denominator value.
For a choice `wf` of one place over each finite base place, the finite sum
of the lift at `wf v` is also that value.

The proof uses `finitePlaceEquiv_under`: an `F`-automorphism preserves the
base place. Thus places above distinct base places are not conjugate.
The published semilocal orthogonality theorem then makes every other
finite local map zero on the section. At its own place, the local map
is a retraction of the section. `finsum_eq_single` reduces the finite
sum to this one term. Finally the inverse local invariant equivalence
recovers the requested denominator value.

All content is derived from the imported Library constructions and Mathlib
finite summation. No new literature theorem is asserted. This file treats
the finite sum only; it does not assert vanishing of archimedean invariants,
the global reciprocity law, descent to idele-class cohomology, or existence
of the global invariant family.
