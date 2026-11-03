# A rational coboundary for a split torus acting linearly on a vector group

This is an internal construction from the published actual-cocycle, finite
linear-action, vector-coordinate and universal split-torus-point interfaces.
Its proof uses finite Laurent coefficients and the cocycle equation directly;
it invokes no external vanishing theorem.

Let `k : Type u` be any field, let `I : Type u` be finite with decidable equality,
and let `T = splitTorus (Spec k) I`. Let `V` be an actual group scheme over
`Spec k` with affine structure morphism, and let `a : AutomorphicAction T V`.
The supplied coordinates
`e W : (W ⟶ V.X) ≃* Multiplicative (Fin d → Γ(W.left, ⊤))`
are required to satisfy the existing `RelativeRoot.IsLinearVectorCoordinates`
predicate: they are natural on every relative test scheme, and the actual
action is scalar-linear over its ring of global functions. No restriction is
placed on the weights or on the characteristic of `k`.

For an actual base cocycle `c : a.Cocycle (Over.mk (𝟙 (Spec k)))`,
`splitTorus.cocycleCoordinates` gives its coordinate vector on each affine
test algebra. `cocycleConstant` is the vector `v₀ : Fin d → k` obtained by
taking the exponent-zero coefficient of these coordinates at the universal
point over the Laurent algebra `k[I → ℤ]`. The construction
`cocycleConjugator` converts `v₀` through the inverse vector coordinates and
the affine self-test isomorphism into an actual morphism `Spec k → V`.

The main identity is `splitTorus.cocycle_eq_coboundary`:
`c = a.coboundary (cocycleConjugator I a e c)`. With the existing coboundary
convention, this says on every relative test that
`c(t) = v * a(t, v⁻¹)`, with `v` pulled back from the constructed rational
point. In additive vector coordinates the formula is `c(t) = v₀ - t·v₀`.
This is equality of actual cocycle morphisms.

The implemented proof proceeds as follows.

1. `AutomorphicAction.Cocycle.baseHom` identifies a base-parametrized cocycle
   with its actual morphism from the acting group. `affineEval` is its
   evaluation on an affine test. Naturality and the cocycle equation follow
   from the existing evaluation laws. `affineEval_ext` proves equality of
   cocycles with affine acting group by testing an affine representative of
   that group itself.
2. `AutomorphicAction.coordinateAction_coeff` shows that the induced finite
   linear action commutes with extraction of every Laurent coefficient when
   the acting point comes from the coefficient algebra. The proof uses
   naturality of the existing action matrix and the finite matrix sum.
   `IsLinearVectorCoordinates.coordinateAction_eq` identifies this induced
   action with the original action in the supplied coordinates.
3. Translating the universal torus point by any affine torus point preserves
   the exponent-zero coefficient of the cocycle: the published translated
   evaluation multiplies the coefficient at exponent `m` by the monomial
   value at `m`, which is one at zero.
4. Apply the actual cocycle equation to the product of that constant torus
   point and the coefficient extension of the universal point. Taking the
   constant coefficient gives `v₀ = c(t) + t·v₀` over every affine
   `k`-algebra. This is
   `cocycleCoordinates_eq_constant_sub_action`.
5. `cocycleConjugator_coordinates` verifies that the constructed base point
   restricts to the scalar extension of `v₀`. The finite product defining
   the split torus is affine: each multiplicative factor is the base change
   of the affine Laurent scheme over `Spec ℤ`. Therefore `affineEval_ext`
   turns the affine coordinate formula into the stated equality of actual
   cocycles.

The auxiliary `Lie.affineSelfTestIso` and its restriction formula identify
the self-algebra affine test with the base scheme. No density of field-valued
points, rational lifting, or separate choices on individual test schemes
enter the proof.

This unit applies to the specified split-torus model with supplied natural
linear vector coordinates. It does not establish linearization of an arbitrary
torus action, descent from a splitting field, or cocycle vanishing for a
nonsplit torus. Those obligations and the full rational conjugacy theorem for
maximal tori remain separate.
