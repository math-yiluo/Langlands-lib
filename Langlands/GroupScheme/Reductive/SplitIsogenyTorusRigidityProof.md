# Isogenies of split reductive groups with the same root characters agree on the torus

This module proves the published proposition
`SplitIsogenyTorusRigidityStatement` (module
[`Langlands.GroupScheme.Reductive.SplitIsogenyTorusRigidityStatement`](SplitIsogenyTorusRigidityStatement.md))
for an arbitrary universe `u`, every field and every pair of split reductive
groups, one of them semisimple, with no further hypothesis.

## Main result

- `splitIsogenyTorusRigidity : SplitIsogenyTorusRigidityStatement.{u}`.

  This is the corrected form of Milne, *Algebraic Groups* (2017),
  Proposition 23.8 (printed p.487) recorded in the statement's Markdown. Let
  `(G, T)` and `(G', T')` be split reductive groups over a field `k`
  (`i : T ⟶ G` and `i' : T' ⟶ G'` split maximal tori), with `G` or `G'`
  semisimple. Let `φ₁ φ₂ : G ⟶ G'` be surjective with finite kernels, and
  let `t₁ t₂ : T ⟶ T'` satisfy `groupHom tₘ ≫ i' = i ≫ φₘ`. If
  `t₁ ≫ α' = t₂ ≫ α'` for every root `α'` of `i'`, then
  `i ≫ φ₁ = i ≫ φ₂`.

## Proof

Since `i ≫ φₘ = groupHom tₘ ≫ i'`, it suffices to prove `t₁ = t₂`.

1. **Isogenies.** Each `φₘ` is an isogeny in the Library's sense
   (`IsIsogeny`: finite, flat and surjective) by
   `FibrewiseCentralIsogenyReduction.isogeny_of_surjective_of_finite_kernel`
   (module
   [`Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyReduction`](FibrewiseCentralIsogenyReduction.md)):
   `G` is smooth, affine and connected, `G'` is smooth and affine, `φₘ` is
   surjective and its kernel is finite.
2. **Root data.** `rootDatumExistence` (module
   [`Langlands.GroupScheme.Reductive.RootDatumExistence`](RootDatumExistence.md))
   gives reduced root data `P` of `i` and `P'` of `i'`, indexed by finite
   types `J` and `J'` in universe `u`.
3. **Isogenies of root data.** `isogenyRootDatum` (module
   [`Langlands.GroupScheme.Reductive.IsogenyRootDatumProof`](IsogenyRootDatumProof.md),
   proving
   [`IsogenyRootDatumStatement`](IsogenyRootDatumStatement.md), Milne
   Proposition 23.5) applied to `φₘ`, `tₘ`, `P` and `P'` gives
   `fₘ : RootDatumIsogeny (ringExpChar k) P' P` whose weight map is
   `χ ↦ tₘ ≫ χ` on the character lattice of `T'`. Only this weight-map
   equation is used from its conclusion.
4. **Agreement on roots.** The roots of `P'` are the roots of `i'`
   (`IsRootDatumOf`), so the hypothesis says
   `f₁.weightMap (P'.root j) = f₂.weightMap (P'.root j)` for every `j : J'`.
5. **Equal weight maps.** `splitSemisimpleRootDatum` (module
   [`Langlands.GroupScheme.Reductive.SplitSemisimplicity`](SplitSemisimplicity.md),
   Milne Proposition 21.48 and its coroot form) turns semisimplicity into
   finite index.
   - If `G` is semisimple, the coroots of `P` span a subgroup of finite
     index in the cocharacter lattice of `T`, and
     `RootDatumIsogeny.weightMap_eq_of_finite_corootSpan` gives
     `f₁.weightMap = f₂.weightMap`.
   - If `G'` is semisimple, the roots of `P'` span a subgroup of finite
     index in the character lattice of `T'`, and
     `RootDatumIsogeny.weightMap_eq_of_finite_rootSpan` gives the same
     equality.

   Both lemmas are in
   [`Langlands.LinearAlgebra.RootDatumIsogenyRigidity`](../../LinearAlgebra/RootDatumIsogenyRigidity.md).
   The first is the source's argument for `G` semisimple: the roots and
   root factors of `f₁` and `f₂` agree because `P` is reduced, so the dual
   maps agree on the coroots. The second is its argument for `G'`
   semisimple.
6. **Conclusion.** Hence `t₁ ≫ χ = t₂ ≫ χ` for every character `χ` of `T'`.
   Characters separate homomorphisms into the split torus `T'`
   (`IsSplitTorus.hom_ext_of_characters`, module
   [`Langlands.GroupScheme.Torus.CharacterIsomorphism`](../Torus/CharacterIsomorphism.md)),
   so `t₁ = t₂`.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
