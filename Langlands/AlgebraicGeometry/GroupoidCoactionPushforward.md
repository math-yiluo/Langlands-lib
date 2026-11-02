# Pushforward along source-cartesian affine relations

This internal algebraic construction gives pushforward of an actual coaction
along a source-cartesian morphism of affine ring equivalence relations. It is
a prerequisite for the finite-cover acyclicity argument. It does not prove
cocycle vanishing or the geometric acyclicity statement.

Let `B`, `C`, `D`, and `P` be commutative rings in an arbitrary universe `u`,
with `B`-algebras `C` and `D` and a `D`-algebra `P`. The source-cartesian
square is supplied in coordinates

```
e : P ≃ₐ[D] D ⊗[B] C.
```

Write `ρ = cartesianBaseMap e : C →+* P`; it sends `c` to
`e.symm (1 ⊗ c)`. The source compatibility is automatic:
`ρ ∘ algebraMap B C = algebraMap D P ∘ algebraMap B D`.
Suppose `t : B →+* C` and `td : D →+* P` define actual
`RingEtaleEquivalenceRelation`s and satisfy the separate target compatibility

```
ρ.comp t = td.comp (algebraMap B D).
```

For any `D`-module `M` in an independent universe `v`, supply its compatible
restricted `B`-module structure. Also supply the compatible `B`-algebra structure
on `P`. The construction `pushforward e ht θ hE hP` takes a
`GroupoidCoaction td M` to a `GroupoidCoaction t M` on that underlying
`B`-module. Neither finiteness of the cover nor finiteness of `M` is required.

The ring-valued point calculations explain why the transferred map satisfies
the full coaction laws. `tensorRingLift` builds the ring homomorphism from
`D ⊗[B] C` associated to compatible ring maps, without requiring a previously
chosen `B`-algebra structure on the target. It temporarily uses the structure
induced by the map from `D`. Composing with `e` gives `cartesianLift`.
Its restrictions to `D` and `C` are the prescribed maps, and
`cartesian_hom_ext` proves uniqueness by tensor induction.

For a base point `φ : C →ₐ[B] S`, `cartesianPoint e φ` is its source-preserving
lift to `D ⊗[B] S`. For composable base points `φ₁` and `φ₂`,
`cartesianFirst e ht φ₁ φ₂ h` lifts `φ₁` with source equal to the target of
the lift of `φ₂`. Target compatibility supplies the balancing equation for
this lift. `cartesianLift_diagonal` uses reflexivity of the covering relation,
uniqueness in the base relation, and source-cartesian uniqueness to show that
a diagonal base point lifts to a diagonal covering point. Similarly,
`cartesian_composite_target` uses transitivity in the covering relation, then
the two uniqueness results, to identify the target of the lifted composite.
The latter yields `cartesianPoint_composite_target` for arbitrary composable
base points. These arguments use the published `hom_ext` theorem for the
base relation; they introduce no descent or vanishing hypothesis.

The module tensor comparison is

```
pushforwardTensorEquiv e : P ⊗[D] M ≃ₗ[B] C ⊗[B] M.
```

It sends `e.symm (d ⊗ c) ⊗ m` to `c ⊗ d • m`. Its implementation first applies
`e` on coefficients, commutes the outer tensor, cancels the `D` base change
using Mathlib's `AlgebraTensorModule.cancelBaseChange`, and commutes the
remaining tensor. The auxiliary comparison `cartesianCancel S` works over
any `B`-algebra `S`. The inverse of the displayed comparison sends `c ⊗ m`
to `ρ(c) ⊗ m`. Multiplication by `ρ(c)` consequently corresponds to
multiplication by `c`.

The pushed additive map is this tensor comparison composed with the original
coaction. Its `t`-semilinearity follows from the original `td`-semilinearity
and target compatibility. `pushforwardTensorEquiv_specialize` shows that
specialization along `φ` commutes with the comparison when the cover point is
`cartesianPoint e φ`. Tensor induction reduces this identity to
`(d ⊗ c) ⊗ m`. `pushforwardTensorEquiv_compose` proves the analogous identity
for pointwise composition. Here the inverse comparison reduces the calculation
to `ρ(c) ⊗ m`, on which the first lifted point acts by `1 ⊗ φ₁(c)`.
The scalar compatibility of `cartesianCancel` and the specialization identity
then finish the calculation. Applying these comparisons to the cover counit
and coassociativity identities gives the actual constructor `pushforward`.
Both laws hold at every test algebra; no test-flatness assumption is added.

The provenance is internal: the point lifts are tensor-product universal
properties, their laws follow from the unchanged published ring-relation
axioms, and the module comparison is ordinary tensor commutation and
base-change cancellation. The file supplies these ring-level constructions
and comparisons only. Extraction of the coordinate equivalence from a scheme
cover, transfer of cocycle vanishing, and geometric Noetherian dévissage are
separate remaining steps of the host task.
