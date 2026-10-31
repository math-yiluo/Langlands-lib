# Geometric connectedness from the generic fibre for smooth proper morphisms

Author: Worker 946. Written for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of
geometric connectedness to finitely generated subalgebras), in a work split with Worker 299.

## Statement

`Langlands.AlgebraicGeometry.NoetherianApproximation.geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd.{u}`

Let `R : Type u` be a noetherian integrally closed domain (`IsDomain R`, `IsNoetherianRing R`,
`IsIntegrallyClosed R`), and let `K : Type u` be a field with `[Algebra R K]` and
`[IsFractionRing R K]`. Let `f : X ⟶ Spec (CommRingCat.of R)` be a morphism of schemes with
`IsProper f` and `Smooth f`. Assume that the generic fibre
`pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) : X ×_R Spec K ⟶ Spec K` is
`GeometricallyConnected`. Then `f` is `GeometricallyConnected`.

All hypotheses are instance arguments except `K` and `f`, which are explicit.

## Provenance

This is an internal helper lemma. It replaces one step of the descent proof of this task as
written in the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`), in the solution module
`S_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd`.
There, the generic fibre is first shown to be geometrically integral with
`AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected`, which depends on
a chain of regular-local-ring modules. Then
`AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_pullback_snd`
is applied; it derives a bijective `appTop` on the generic fibre from geometric reducedness and
geometric connectedness. Here the published Library theorem on smooth proper geometrically
connected schemes over a field gives that bijectivity directly from smoothness. So neither FLT
lemma, nor the regular-local-ring chain, is needed.

## Proof

1. Write `g` for the generic fibre
   `pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))`. Mathlib's base-change
   instances make `g` smooth and proper, and `g` is geometrically connected by hypothesis.
   The Library theorem `Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`
   (module `Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof`), applied
   to `K` and `g`, gives `IsIso g.appTop`.
2. `ConcreteCategory.bijective_of_isIso` turns this into bijectivity of `g.appTop`.
3. Smoothness implies flatness, by Mathlib's instance `Smooth f → Flat f`. The ported FLT theorem
   `AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`
   (module
   `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`)
   applies to `K`, `f` and that bijectivity, and concludes that `f` is geometrically connected.
   Its Markdown describes how it is proved.

## Imports

`Mathlib`, the Library module
`Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof`, and the ported FLT
module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`.
