# Algebra structure on canonical global-functions base change

This internal construction upgrades the canonical module comparison in
`FieldGlobalFunctions` to an equivalence of the actual global-functions
algebras. All schemes and commutative rings lie in an arbitrary universe
`u`. It is a construction prerequisite for the proper-field Picard argument.

For `f : X → Spec R`, `GlobalFunctionsAlgebra.algebra f` is the algebra
structure induced by `DerivedSections.structureRingHom f`, namely
`ΓSpecIso.inv` followed by the actual pullback of functions along `f`.
The algebra structure is an explicit local choice throughout, so it
specifies the scalar action without adding a global instance.

For arbitrary commutative rings `R`, `S`, a ring map `φ : R → S`, and
morphisms `f : X → Spec R`, `f' : Y → Spec S`, `g : Y → X` with
`g ≫ f = f' ≫ Spec.map φ`, `baseChangeMap` is the canonical `S`-algebra map
from `S ⊗[R] Γ(X, O_X)` to `Γ(Y, O_Y)`. The equality
`structureRingHom_naturality` proves compatibility of `g.appTop` with the
two structure homomorphisms. After installing the composite `R`-algebra
structure on `Γ(Y, O_Y)` and its scalar tower, `AlgHom.liftEquiv` constructs
the map from this actual pullback homomorphism. Its pure-tensor formula is
`s ⊗ a ↦ structureRingHom(f')(s) * g.appTop(a)`. This construction needs
only the commuting square.

For a field `k`, assume `f : X → Spec k` is proper, take any commutative
ring `S` and ring map `φ : k → S`, and assume the displayed square is
Cartesian. Then `FieldGlobalFunctions.finite_algebra` proves
`Module.Finite k Γ(X, O_X)` for the structure-morphism algebra action, and
`FieldGlobalFunctions.baseChangeAlgebraEquiv` is an `S`-algebra equivalence
`S ⊗[k] Γ(X, O_X) ≃ₐ[S] Γ(Y, O_Y)` with the same pure-tensor formula.
There is no additional assumption on `S`, including no noetherianity or
nontriviality assumption. No equality between `Γ(X, O_X)` and `k` is used.

The proof first identifies the structure-sheaf pullback comparison under
its adjunction: `pullbackUnitIso_unit` states that the adjunction unit,
followed by the pushforward of the canonical `g*O_X ≅ O_Y`, is the actual
map `O_X → g*O_Y`. Combining this identity with
`scalarSectionsBaseChangeMap_one_tmul` identifies the image of `1 ⊗ a`
under the canonical sections base-change isomorphism with `g.appTop a`.
Linearity gives the formula on every pure tensor. These identities are
internal consequences of Mathlib's definition of the unit structure-sheaf
comparison and the published scalar sections comparison.

`baseChangeAlgebraLinearEquiv` transports the module isomorphism
`FieldGlobalFunctions.baseChangeIso` through
`Langlands.Scheme.Modules.extendScalarsAlgebraEquiv`, which compares the
categorical extension-of-scalars module with the ordinary algebra tensor
product. The pure-tensor formulas prove equality with
`baseChangeMap` as linear maps by tensor induction. The resulting bijectivity
allows `AlgEquiv.ofBijective` to construct `baseChangeAlgebraEquiv`.
It retains the same pure-tensor formula. `finite_algebra` uses
`FieldGlobalFunctions.finite` with the definitionally matching
structure-map algebra action.

The construction preserves arbitrary fields and arbitrary proper schemes;
there is no projectivity, smoothness, reducedness, connectedness or
rational-point premise. It supplies affine algebra base change and
finiteness. Arbitrary-base direct-image comparison, an automorphism group
scheme, topology comparison and Picard representability remain separate
obligations.
