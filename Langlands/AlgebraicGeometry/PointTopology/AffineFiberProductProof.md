# Proof of the affine fibre-product topology statement

Proof author: Worker 16. Verification and submission: Worker 100.

Proof of `Langlands.AlgebraicGeometry.PointTopology.AffineFiberProductTopologyProperty`
(module `AffineFiberProductStatements`): the fibre-product part of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and its proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The entry theorem is `affineFiberProductTopology_proof R C A B S`. It has exactly the
hypotheses of the target: five commutative rings in a common universe, compatible
`R`- and `C`-algebra structures on `A` and `B`, an `R`-algebra `S`, and a topology on
`S` making it a topological ring. It shows that `specFiberProductPointPairEquiv`,
from actual `S`-points of `Spec A ×[Spec C] Spec B` over `Spec R` to compatible pairs
of factor points, is a homeomorphism for the published topologies. Conrad's proof
reduces to closed immersions through the separatedness of affine schemes; the Lean
proof is direct.

## Route

All auxiliary declarations are in namespace
`Langlands.AlgebraicGeometry.PointTopology.AffineFiberProductProof`.

- **Composition with `Spec` of an algebra map.** For `φ : A →ₐ[R] D` and an actual
  point `q` of `Spec D` over `Spec R`, `comap φ q` is `q ≫ Spec.map φ`, which stays
  over `Spec R` (`specMap_comp_algebraMap`). `specPointEquiv_comap` proves that the
  published comparison `specPointEquiv` sends it to `AlgPoint.precomp φ`: both ring
  maps have the same `Spec` (`Spec.map_preimage`, `Spec.map_comp`) and `Spec` is
  faithful. Hence `comap φ` is continuous (`continuous_comap`), being a composite of
  the published `specPointHomeomorph` and its inverse with the continuous
  precomposition. The proof imports only the published fibre-product statement
  module; it is independent of the sibling product proof.
- **Components.** `inclLeft` is the left tensor inclusion `A →ₐ[R] A ⊗[C] B`, and
  `inclRight` the right tensor inclusion with scalars restricted to `R`. By Mathlib's
  `pullbackSpecIso_hom_fst` and `pullbackSpecIso_hom_snd`, the two components of the
  comparison are `comap inclLeft` and `comap inclRight` applied to the published
  tensor-coordinate point `specFiberProductTensorEquiv p` (`pair_fst`, `pair_snd`).
  So the comparison is continuous into the product and into its compatible-pair
  subspace (`continuous_pair`).
- **Inverse.** The inverse is the published pullback lift. Applying `pair_fst` and
  `pair_snd` to a lifted pair, and the identity `pair ∘ lift = id`, the
  tensor-coordinate point of the lift takes at `a ⊗ 1` and `1 ⊗ b` the coordinate
  values of the first and second factor points (`lift_tmul_one`, `lift_one_tmul`).
  By the published homeomorphisms it suffices to show that this tensor-coordinate
  point depends continuously on the pair, coordinate by coordinate
  (`AlgPoint.continuous_iff`). Induction on the tensor (`TensorProduct.inductionOn`)
  uses `a ⊗ b = (a ⊗ 1)(1 ⊗ b)`, multiplicativity and additivity of the point, and
  continuity of multiplication and addition in `S` (`continuous_lift`).
- **Conclusion.** `pairHomeomorph` packages the published equivalence with both
  continuity proofs; its underlying map is `specFiberProductPointPairEquiv`.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
