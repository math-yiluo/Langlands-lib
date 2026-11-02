# Actual split-torus coordinates as a multiplicative homeomorphism

Worker 112, using the actual-point topology support by Worker 94.
This is an internal comparison construction from the published categorical
split torus and its published Laurent-algebra model. No new identification
of algebraic groups is assumed.

Let `I : Type u` have a `Fintype` instance, let `R : CommRingCat`, and let
`A : CommAlgCat R` carry a topology making it a topological ring. The carrier
`(splitTorus (Spec R) I).affinePoints A` consists of actual morphisms over
`Spec R` from `Spec A` to the existing categorical product of copies of
`Gm`. It has `GroupScheme.affinePointsTopologicalSpace`, the topology induced
by all global regular-function evaluations. The target `I → Aˣ` has the
existing product topology, with the units topology recording both a unit
and its inverse. Neither a Hausdorff hypothesis nor continuity of the
base algebra map is needed. The index type may be empty.

`affineUnitsEquiv` is a typed wrapper for the existing
`splitTorus.affinePointsEquiv`; it changes neither its function nor its
inverse. `affinePointsHomeomorph` bundles this same multiplicative
bijection with proofs of continuity in both directions.

The implementation proves the following comparisons and continuity facts.

- `algHomEquiv_symm_single` evaluates the Laurent classifying algebra map
  at a basis monomial `single m r` as the image of `r` times the finite
  product of the coordinate units to the integer powers `m i`.
  `continuous_laurentClassify` then proves continuity for every Laurent
  algebra element by monoid-algebra induction: monomials use continuous
  integer powers in the unit group, sums use addition, and scalar
  multiplication uses the algebra-map identity and multiplication.
- `laurentAffinePointsEquiv` is the published corepresented affine point
  equivalence of the actual Laurent group scheme. Its inverse is exactly
  the spectrum map of the classifying algebra homomorphism.
  `affinePointEvaluation_map_laurentClassify` identifies evaluation at
  that point with evaluation of the algebra homomorphism, by naturality
  of the spectrum/global-sections isomorphism. This proves
  `continuous_laurentAffinePointsEquiv_symm` using the existing topology.
- `continuous_affinePointsEquiv` proves forward continuity directly from
  each actual categorical projection and the existing continuous
  `Gm.affineUnitsEquiv`. This direction only needs a topology on `A`.
- `laurentAffinePointsEquiv_laurentIso` proves that the published
  `splitTorus.laurentIso` acts as the identity on these coefficient-unit
  coordinates. It uses `isoOfPointModels_hom`, the published comparison
  of corepresented affine and global-section coordinates, and cancellation
  of the spectrum/global-sections isomorphism. Thus the inverse of the
  original coordinate equivalence is the Laurent classifier followed by
  the inverse scheme isomorphism. Postcomposition by that morphism is
  continuous in the existing point topology. This proves
  `continuous_affinePointsEquiv_symm` and the bundled homeomorphism.

The topology on actual points is the regular-evaluation topology already
used by the ambient point constructions; it is not defined using this
homeomorphism. This file supplies the general coefficient-ring comparison
needed to transport the positive-real idele embedding to actual split
adelic torus points. It contains no adelic measure, reduction-theory or
finite-volume assertion.
