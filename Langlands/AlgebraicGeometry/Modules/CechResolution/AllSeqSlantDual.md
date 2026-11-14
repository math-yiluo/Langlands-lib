# Shuffle slant from an actual degree-one cohomology dual

This is an internal construction for the degree-two exterior and canonical coproduct comparison. It supplies the cochain functional required by `AllSeq.slantCanonical` starting from an arbitrary linear dual of actual structure-sheaf H¹. It uses only vector-space splitting and the existing ordered Čech class and comparison maps. No new external geometric assertion is assumed.

All declarations are in `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`. The field and schemes have universe `u`, and the finite cover index types have that same universe.

## Extending the class map

Let `K` be a field, let `π : X ⟶ Spec K`, let `U` be a finite indexed family of open subsets, and let `M` be an actual sheaf of modules on `X`. Neither separatedness nor a covering or affineness condition is required for this first construction.

For each natural number `n`, write `Z` for the kernel of the ordered Čech differential in degree `n + 1`. The inclusion `Z.subtype` is an injective `K`-linear map. Mathlib's `LinearMap.leftInverse` supplies a chosen linear retraction `r` of that inclusion, using vector-space splitting. Define

```text
cochainClassExtension n = classMap n ∘ r.
```

This is a linear map from all cochains in degree `n + 1` to the homology of the actual ordered Čech complex in that degree. It is an extension, not a canonical assignment of a cohomology class to a noncocycle. The chosen retraction and its values on noncocycles are part of the construction.

`cochainClassExtension_cocycle` uses `LinearMap.leftInverse_apply_of_inj` and `Submodule.ker_subtype` to identify the value on a cocycle with its existing `classMap` class. `cochainClassExtension_dCochain` first applies `dCochain_comp_dCochain` to see that a coboundary is a cocycle. The cocycle formula and `classMap_eq_zero_iff` then give zero, with the original cochain as a boundary witness.

## Actual cohomology and its dual

Now assume `π` is separated, the family `U` covers `X`, and every `U i` is affine. The structure-sheaf specialization transports the extension through the actual acyclic-resolution comparison:

```text
canonicalClassExtension n = cohomologyEquiv (n + 1) ∘ cochainClassExtension n.
```

Its codomain is `(relativeCohomology π (n + 1)).obj (unitModule X)`, the actual right-derived structure-sheaf cohomology. `canonicalClassExtension_cocycle` identifies its value on a cocycle with `canonicalClass n`. `canonicalClassExtension_dCochain` proves that every degree-`n` coboundary maps to zero.

Suppose also that the section rings carry `K`-algebra structures induced by `secHom π`, expressed by the explicit compatibility hypothesis `halg`. For an arbitrary actual degree-one cohomology dual `ell`, define

```text
h1DualCochainFunctional ell =
  ell ∘ canonicalClassExtension 0 ∘ (cochainSecEquiv 1)⁻¹.
```

The domain of the resulting functional is all raw first-factor one-cochains, the families `σ ↦ Γ(X, inter U σ)` for two-entry tuples `σ`. Its scalar action is precisely the supplied section-ring action. `h1DualCochainFunctional` is itself a linear map in `ell`, since the chosen retraction is fixed before composing with the dual.

`h1DualCochainFunctional_cocycle` says that its value on the raw section family of a cocycle `z` is `ell (canonicalClass 0 z)`. `h1DualCochainFunctional_d` says that it annihilates `Cech.d 0 c` for every raw zero-cochain `c`. This follows from `dCochain_unit` and the preceding boundary formula; it is exactly the closedness hypothesis required by `slantCanonical`.

## Slant from the dual

`slantByH1Dual n` applies `slantCanonical n` with the functional just constructed and its proved boundary-vanishing property. Its source and target are the actual cohomology modules

```text
H^(n + 1)(P, O_P) →ₗ[K] H^n(Y, O_Y).
```

The data retained by this definition are an actual pullback square with maps `p₁ : P ⟶ X` and `p₂ : P ⟶ Y` over `Spec K`; separated structure maps for `X`, `Y`, and `P`; compatible structure-induced section algebra actions on all three schemes; and the equality `p₁ ≫ πX = πP`. It also retains finite open families `U` and `V`, the covering and affine-member hypotheses for `U`, `V`, and their product family, affine two-entry intersections for `U`, and affine nonempty finite intersections for `V`. No nonzero or normalized dual is required, and there is no characteristic restriction. The definition is an instantiation of the existing slant construction, including target degree zero.

The chosen covers and vector-space retraction remain in the construction. Independence of the retraction or covers on cohomology is not proved here. General creation–contraction identities, mixed tensor detection, alternation, exterior generation, and the host exterior/coproduct comparison also remain open. This unit only supplies the actual H¹-dual input to the previously constructed slant maps.
