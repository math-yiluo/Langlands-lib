# Canonical affine-chart comparison maps for relative differentials

Let `f : X ⟶ S` be any morphism of schemes, let `U` and `V` be affine opens of `S` and `X`, and suppose `e : V ≤ f ⁻¹ᵁ U`. Write `R = Γ(S, U)`, `A = Γ(X, V)`, and `φ = f.appLE U V e : R ⟶ A`. Every occurrence of `KaehlerDifferential R A` below uses the algebra structure `φ.hom.toAlgebra`. This module constructs the two canonical maps used to compare the actual restriction of `relativeDifferentials f` with the algebraic affine model. It does not assert their invertibility or construct the final comparison isomorphism.

Put `g = hV.fromSpec : Spec A ⟶ X`, `b = hU.fromSpec : Spec R ⟶ S`, `q = hV.isoSpec.hom : V.toScheme ⟶ Spec A`, and `f′ = Spec.map φ`. Mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec` supplies `g ≫ f = f′ ≫ b`. Applying the existing `relativeDifferentialsSquareMap` to this square defines `relativeDifferentialsAffineChartSquareMap : g* Ω(X/S) ⟶ Ω(Spec A/Spec R)`. Here and throughout, Ω denotes the existing sheafification-based `relativeDifferentials`; it is not redefined.

The lemma `relativeDifferentialsAffineChartSquareMap_adjoint_app` describes the pullback–pushforward adjoint of this map on every open `W` of `X`: it sends the actual differential of `a : Γ(X, W)` to the actual differential of `g.app W a` on `g ⁻¹ᵁ W`. The lemma `relativeDifferentialsAffineChartSquareMap_unique_of_app` proves that these values determine the square map uniquely. Both are specializations of the published canonical-square API, so the construction preserves the universal derivation.

The isomorphism `relativeDifferentialsAffineChartPullbackIso` identifies the actual restricted sheaf `Ω(X/S).restrict V.ι` with `q* g* Ω(X/S)`. It composes Mathlib's restriction-to-pullback isomorphism, the equality `q ≫ g = V.ι`, and the pullback-composition isomorphism. Composing its forward map with the pullback of the chart-square map gives `relativeDifferentialsAffineChartToSpecMap`.

The object `relativeDifferentialsAffineChartModel` is `q* tilde(Ω(A/R))`. The map `relativeDifferentialsAffineChartFromModelMap` is the pullback along `q` of the published `relativeDifferentialsSpecMap R A`. Thus there is a canonical diagram in `V.toScheme.Modules`:

```text
Ω(X/S).restrict V.ι  ──ToSpecMap──▶  q* Ω(Spec A/Spec R)
                                          ▲
                                          │ FromModelMap
                                          │
                                    q* tilde(Ω(A/R))
```

The source of `FromModelMap` uses the specified ring-map algebra structure, and its target is the same object as the target of `ToSpecMap`. Its underlying Spec map satisfies the published `relativeDifferentialsSpecMap_app_toOpen_D`: on every open of `Spec A`, the algebraic differential of a global element `a : A` maps to the actual differential of the restriction of the corresponding global section. This is an imported compatibility result, not a new assertion here about arbitrary sections after pullback.

For any algebraic basis `b : Module.Basis ι A (KaehlerDifferential R A)`, `relativeDifferentialsAffineChartModelBasisIso` constructs an isomorphism from the model to the free module sheaf on `ι` over `V.toScheme`. It applies the tilde functor to `b.repr.toModuleIso`, composes with `tildeFinsupp`, pulls back along `q`, and uses `SheafOfModules.pullbackObjFreeIso`. This gives a trivialization of the model only. Transporting it to the actual restricted differential sheaf still requires the missing comparison isomorphism.

The geometric source is the Stacks Project, Morphisms §29.33 (tag 01UM), Definition 29.33.1 and Lemmas 29.33.3–5, in registered source `stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`. Locality and the affine differential comparison motivate the diagram; their invertibility conclusions are not proved by this module. The constructions here are derived from the existing square map, Spec map, and Mathlib's affine-chart and module-sheaf APIs. The model basis isomorphism is an internal consequence of the usual basis representation and preservation of free sheaves under pullback. No smoothness, finite type, reducedness, nonzero-ring, or nonemptiness hypothesis is used, and the index type of the basis need not be finite.
