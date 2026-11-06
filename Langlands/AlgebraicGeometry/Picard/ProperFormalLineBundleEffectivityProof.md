# Proper formal line-bundle effectivity over complete local rings

`Langlands.AlgebraicGeometry.Picard.properFormalLineBundleEffectivity` proves
`ProperFormalLineBundleEffectivityStatement.{u}` for every universe `u`.
For every complete local noetherian commutative ring `R`, proper morphism
`f : X ⟶ Spec R`, and compatible system `F` of actual line bundles on
`X_n = X ×[Spec R] Spec(R / m^(n+1))`, where `m` is the maximal ideal, it
produces an actual line bundle `L` on `X` with a single comparison between
its ordinary restriction system and `F`, commuting with every specified
transition. There is no projectivity, flatness, smoothness, residue-field,
or characteristic restriction.

The implemented proof is the application

```lean
properFormalLineBundleEffectivity_of_coherentExistence
  Modules.properFormalCoherentExistence
```

The imported theorem `Modules.properFormalCoherentExistence` proves the
unconditional coherent formal existence proposition. Its module
`Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceProof`
applies the actual-sheaf reduction to the ported Anthropic FLT
Grothendieck-existence theorem. Its input, realization and comparison
bridges preserve the actual thickenings and all transition equations.

The supporting module `ProperFormalLineBundleEffectivityReduction`,
included with this proof, derives the required rank-one specialization:

1. Forget rank one using `FormalLineBundleSystem.toModuleSystem`.
   This retains the module sheaves and their specified transition
   isomorphisms. Each term is locally finitely presented because it is
   locally free of rank one.
2. Coherent existence gives a locally finitely presented module sheaf `M`
   on `X` and one `FormalModuleSystem.Comparison` between its ordinary
   restrictions and the forgotten system. Its component isomorphisms
   show that each ordinary adic pullback of `M` is locally free of rank one.
3. Properness over the noetherian base makes `X` locally noetherian and
   makes `f` universally closed. `lineBundleOfAdicPullbacks` then promotes
   `M` to a line bundle `L` with underlying module definitionally `M`.
   This constructor uses quotient-stalk frames for all powers of the
   extended maximal ideal at closed-fibre points, local rank-one
   reflection, and universal closedness over the local base to extend
   the rank-one locus to all of `X`.
4. `FormalLineBundleSystem.isAlgebraization_of_module` lifts the original
   module comparison to the full subcategory of line bundles. It retains
   every transition square, yielding `FormalLineBundleSystem.IsAlgebraization L F`.

This is the derived rank-one specialization of coherent Grothendieck
existence described in Stacks Project Proposition 30.25.4 (Tag 088C), with
actual compatible systems as in Section 30.27, Remark 30.27.2 (Tag 088F).
The registered source is
`stacks-formal-line-bundle-effectivity-2026-11-03`, files `088C.html` and
`0CYW.html`. The implemented proof uses the Library's coherent-existence
and rank-one-promotion theorems; the supporting Markdown explains their
separate arguments. Only existence of a compatible algebraization is
asserted here; full faithfulness of completion is a separate result.
