# Pushforward of the augmented inverse-image Čech complex

This internal construction concerns an affine morphism `g : Y ⟶ X`, an ordered
affine cover `𝒰` of `X`, and an arbitrary module sheaf `N` on `Y`, in a common
arbitrary universe `u`. It identifies the actual map from the Čech complex
of `g_* N` to the pushforward of the Čech complex on the full inverse-image
cover. It proves that pushing forward this particular augmentation
preserves its quasi-isomorphism property.

The construction uses the actual `sheafOnPushforward`, `cechPushforward`,
their augmentation identity, and the contracting-homotopy exactness result
for the sheafified Čech complex. This is an internal consequence, with no
independent external theorem or relative cube conclusion asserted.

For any isomorphism `a : M ⟶ g_* N` and opens `W' = g ⁻¹ᵁ W`,
`isIso_sheafOnPushforward_of_isIso` proves that the specified
`sheafOnPushforward g a` factor map is invertible. Its component over
`V` is the composite of the invertible section map of `a` over `W ⊓ V`
and restriction in `N`. The latter restriction is along the equality
`W' ⊓ g ⁻¹ᵁ V = g ⁻¹ᵁ (W ⊓ V)`. Replacing its order-category morphism
by `eqToHom` makes its invertibility immediate. The component criterion
for module-sheaf isomorphisms concludes. This individual factor result
does not require `g` to be affine.

For the rest of the file, affineness of `g` ensures that the full inverse
images of the affine cover charts form an ordered affine cover. The
intersections in this cover are precisely the full preimages of the
source intersections.

`cechTermPushforward_comp_mapBiproduct` identifies the actual degree map,
followed by the canonical pushforward-biproduct comparison, with the
biproduct of its actual factor maps. Projection to each intersection
proves this equality, using `cechTermPushforward_π` and the projection
formulas for the two biproduct maps. Pushforward preserves these finite
biproducts because it is an additive right adjoint.

`isIso_cechTermPushforward_of_isIso` applies the factor theorem and
forms the biproduct of its isomorphisms. The preceding equality then
proves invertibility of the degree map by cancellation of the
pushforward-biproduct isomorphism.
`isIso_cechPushforward_of_isIso` applies the component criterion for
isomorphisms of complexes.

`cechPushforwardIso` specializes the coefficient map to the identity
of `g_* N` and packages the resulting `cechPushforward` as an
isomorphism. `cechPushforwardIso_hom` records that its forward map is
exactly that specified cochain map.
`cechAug_cechPushforwardIso` specializes the previously implemented
augmentation square: the source Čech augmentation followed by this
forward map is exactly `mapResolutionAugmentation g_*` of the target
Čech augmentation.

Finally, `quasiIso_pushforward_cechAug` rewrites by this augmentation
identity. The source augmentation is a quasi-isomorphism by
`quasiIso_cechAug`, and the forward map of `cechPushforwardIso` is an
isomorphism. Their composite is therefore a quasi-isomorphism.

These conclusions require no quasi-coherence, separatedness, flatness
or higher-direct-image vanishing hypothesis on `N`. They establish the
pushforward of this particular augmentation as a right resolution.
They do not claim that pushforward preserves arbitrary
quasi-isomorphisms or prove acyclicity of the Čech terms for relative
sections. Those term-acyclicity inputs remain necessary for the intended canonical
cohomology base-change application.
