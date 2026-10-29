# Proof that closed loci detected on affine charts glue

`Langlands.AlgebraicGeometry.closedLocusFromAffineCharts` proves
`Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsStatement.{u}`. See
`ClosedLocusFromAffineChartsStatement.md` for the exact statement.

## Provenance and licence

The proof is adapted from the namespace `GlueClosed2` in the module
`P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart.lean`
of the Anthropic FLT Lean source at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`
(`anthropic-flt-complete-lean-source-6e837e75`). That source is licensed under
the Apache License 2.0, and the Lean file carries an attribution header. The
adaptation makes these changes:

- the FLT triviality predicate `Triv` on pullbacks of a rigidified line
  bundle is replaced by an arbitrary predicate `P`;
- the FLT lemma `Triv.comp` becomes hypothesis 1 of the statement;
- in the FLT proof, the step "factoring implies triviality" glues local
  trivializations using a hypothesis `hH0` on global functions; here that
  step is hypothesis 2 instead;
- universe `0` becomes `u`;
- the morphisms over a base `Spec R` become plain morphisms into `X`;
- a few rewrites are adjusted to the pinned Mathlib.

## Proof outline

Write `P` for the predicate, and fix a chart `(Z_U, ι_U)` for every affine open
`U`. This choice is packaged in the structure `Chart P U`. Put
`emb_U = ι_U ≫ U.ι : Z_U ⟶ X`.

1. **Charts in terms of `X` (`Chart.iff'`).** Let `ψ : Y ⟶ X` have image in
   `U`. Then `P ψ` holds if and only if `ψ` factors through `emb_U`. The proof
   lifts `ψ` through the open immersion `U.ι`
   (`IsOpenImmersion.lift`) and applies the chart property. In particular
   `P emb_U` holds (`Chart.prop_emb`).
2. **The ideals.** For an affine open `V`, put
   `κ V = ker (emb_V.app V) ⊆ Γ(X, V)`.
3. **Compatibility of the charts (`ker_emb_app_eq`).** If `V ≤ U` are affine
   opens, then `ker (emb_U.app V) = κ V`. For one inclusion, `emb_V`
   satisfies `P` and has image in `U`, so it factors through `emb_U` by step 1.
   For the other, the restriction of `emb_U` to `emb_U⁻¹(V)` satisfies `P`
   by hypothesis 1. It has image in `V`, so it factors through `emb_V`. The
   kernel of `emb_U.app V` equals the kernel of this restriction on
   `Γ(X, V)` (`ker_app_res`).
4. **Basic opens (`ker_emb_app_map_basicOpen`).** For an affine open `W` and
   `s ∈ Γ(X, W)`, the extension of `κ W` to `Γ(X, D(s))` is
   `ker (emb_W.app D(s))`. Here `Γ(X, D(s))` is the localization of
   `Γ(X, W)` at `s`. The inclusion `⊆` is naturality. For `⊇`, an element
   of the kernel is `x / s^n`. Because `emb_W⁻¹(W)` is quasi-compact, the
   lemma `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`
   gives `s^m x ∈ κ W`.
5. **The glued ideal sheaf (`glued`).** By steps 3 and 4 the ideals `κ V`
   satisfy the axiom `map_ideal_basicOpen` of `X.IdealSheafData`. Let `I` be
   the resulting ideal sheaf. Its closed subscheme `I.subscheme` with the
   closed immersion `I.subschemeι` is the required `Z` and `ι`.
6. **Factoring implies `P`.** Suppose `ψ = ψ₀ ≫ I.subschemeι`. Then
   `I ≤ ker ψ`, so `κ V ≤ ker (ψ.app V)` for every affine `V`. By hypothesis 2
   it suffices to show `P` for the restriction of `ψ` to `ψ⁻¹(V)`. That
   restriction lifts to a morphism `k` into `V`. The comparison
   `ker_comp_ι_app` identifies kernels on `Γ(X, V)` with kernels on `Γ(V, ⊤)`
   through the isomorphism `θ V`. From it, `ker ι_V ≤ ker k` as ideal sheaves
   on the affine scheme `V` (`Scheme.IdealSheafData.le_of_isAffine`). So `k`
   factors through the closed immersion `ι_V` (`IsClosedImmersion.lift`), and
   step 1 gives `P`.
7. **`P` implies factoring.** Suppose `P ψ`. For every affine `V`, the
   restriction of `ψ` to `ψ⁻¹(V)` satisfies `P` by hypothesis 1, so it factors
   through `emb_V` by step 1. Hence `κ V ≤ ker (ψ.app V)` (using `ker_app_res`
   again). By `Scheme.IdealSheafData.le_ofIdeals_iff` this gives `I ≤ ker ψ`,
   so `ψ` factors through `I.subschemeι` by `IsClosedImmersion.lift`.

The final theorem picks one chart for each affine open from hypothesis 3 by
choice and applies `ClosedLocusFromAffineCharts.main`.
