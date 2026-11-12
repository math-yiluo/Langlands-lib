# Proofs of the affine product statements

Proof author: Worker 16. Checked and submitted by Worker 99.

Proof of `Langlands.AlgebraicGeometry.PointTopology.AffineProductProperties`
(module `AffineProductStatements`): the product part of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Proposition 2.1
and its proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The entry theorem is `affineProductProperties_proof R A B S`, for commutative rings
`R`, `A`, `B`, `S` in a common universe with `R`-algebra structures on `A`, `B`, `S`
and any topology on `S`. It proves the three conjuncts of the target. The module
also proves `tensorProductTopologyProperty_proof`, the statement
`TensorProductTopologyProperty R A B S` with the four rings in independent universes.
This is the intrinsic evaluation-topology extension of Conrad's finite-type
product assertion: every tensor is a finite sum of pure tensors, so the argument
applies to arbitrary coordinate algebras. The scheme projection identification
is a derived comparison with Mathlib's actual pullback.
No finite generation, Hausdorffness, locality or topology on `R`, `A`, `B` is used;
the topological clauses use only that `S` is a topological ring, as in the target.

## Route

- **Arithmetic of points.** `AlgPoint.apply_zero`, `apply_one`, `apply_add` and
  `apply_mul` restate the algebra-map identities for the named point carrier.
- **Continuity criterion on tensor coordinates.** `AlgPoint.continuous_of_tmul`:
  for an `R`-algebra tower `R → C`, a map `f : T → AlgPoint R (A ⊗[C] B) S` is
  continuous if `t ↦ f t (a ⊗ 1)` and `t ↦ f t (1 ⊗ b)` are continuous for all `a`,
  `b`. By the universal property of the evaluation topology (`continuous_iff`) it
  suffices to treat each coordinate `z`; induction on `z` (`TensorProduct.inductionOn`)
  uses `a ⊗ b = (a ⊗ 1)(1 ⊗ b)` and continuity of multiplication and addition in `S`.
- **Tensor points.** The inverse `tensorPointLift` of the published restriction map
  takes the value `p a * q b` on `a ⊗ b`; at `a ⊗ 1` and `1 ⊗ b` it is the coordinate
  evaluation of `p` or `q`, so it is continuous by the criterion
  (`continuous_tensorPointLift`). With the published `continuous_tensorPointPair`
  this gives the homeomorphism `AlgPoint.tensorPointHomeomorph`, whose underlying
  map is `tensorPointPair`; hence `TensorProductTopologyProperty`.
- **Composition with `Spec` of an algebra map.** For `φ : A →ₐ[R] D` and an actual
  point `q` of `Spec D` over `Spec R`, `specPointComap φ q` is the composite
  `q ≫ Spec.map φ`, which stays over `Spec R` (`specMap_algHom_comp_algebraMap`).
  `specPointEquiv_specPointComap` proves that the published affine comparison
  `specPointEquiv` sends it to the precomposition `AlgPoint.precomp φ`: both ring
  maps have the same `Spec`, by `Spec.map_preimage` and `Spec.map_comp`, and `Spec`
  is faithful.
- **Projection identification.** The two components of `specProductPointPairEquiv`
  are `specPointComap` of the left and right tensor inclusions applied to the point
  `p ≫ (pullbackSpecIso R A B).hom` (`specProductPointPairEquiv_fst`, `_snd`).
  Mathlib's `pullbackSpecIso_hom_fst` and `pullbackSpecIso_hom_snd` turn these
  composites into `p ≫ pullback.fst` and `p ≫ pullback.snd`
  (`specProductProjection_proof`).
- **Scheme product topology.** `specProductPointPairEquiv` is by definition the
  composite of the published `specProductTensorEquiv`, `specPointEquiv`,
  `tensorPointEquiv` and the inverses of the two factor comparisons. Each is the
  underlying equivalence of a homeomorphism (`specProductTensorHomeomorph`,
  `specPointHomeomorph`, `tensorPointHomeomorph`), so the composite homeomorphism
  has the same underlying map (`specProductTopology_proof`).

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
