# Proper formal line-bundle effectivity from coherent formal existence

`properFormalLineBundleEffectivity_of_coherentExistence` proves that
`Modules.ProperFormalCoherentExistenceStatement.{u}` implies
`ProperFormalLineBundleEffectivityStatement.{u}`. It is a reduction only: it
does not prove coherent formal existence, which remains a separate hypothesis.
The companion module `ProperFormalLineBundleEffectivityProof` discharges this
hypothesis with `Modules.properFormalCoherentExistence`. The reduction below
is a derived argument using coherent existence and rank-one promotion.

Fix a complete local noetherian ring `R` with maximal ideal `m`, a proper
morphism `f : X ⟶ Spec R` and an actual system `F` of line bundles on the
thickenings `X_n = X ×[Spec R] Spec(R / m^(n+1))`, with specified
ordinary-pullback transition isomorphisms.

1. Forget local rank one with `FormalLineBundleSystem.toModuleSystem`. This
   keeps the same module sheaves and the same transition isomorphisms. Each
   term is locally finitely presented by
   `IsLocallyFreeRankOne.isFinitePresentation`.
2. The coherent-existence hypothesis gives a locally finitely presented
   module sheaf `M` on `X` and one comparison `e` between the ordinary
   restriction system of `M` and the forgotten system, commuting with every
   transition.
3. For each `n`, the component `e.component n` is an isomorphism from the
   ordinary pullback of `M` to `X_n` onto the line bundle `F.obj n`. So that
   pullback is locally free of rank one by `IsLocallyFreeRankOne.of_iso`.
4. Properness makes `f` universally closed and of finite type. Since `R` is
   noetherian, `X` is locally noetherian by
   `LocallyOfFiniteType.isLocallyNoetherian`. Then
   `lineBundleOfAdicPullbacks f M` makes `M` itself a line bundle `L`. Its
   underlying module is definitionally `M`.
5. `FormalLineBundleSystem.isAlgebraization_of_module` takes the comparison
   `e` from step 2 and lifts it through the full subcategory of line bundles,
   after composing with the identity-component comparison between the
   restriction system of `L` and the ordinary restrictions of `M`. Every
   transition square is kept, so `L` algebraizes `F` in the required sense.

Completeness of `R` is used only through the coherent-existence hypothesis.
The rank-one promotion in step 4 needs only a local base, a locally
noetherian source and universal closedness. No projectivity, flatness,
residue-field or characteristic assumption is added.
