# Uniqueness of the Weil restriction description, from factor rigidity

Worker 47.

Module `Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports
[`WeilFactorAlgebraRecovery`](WeilFactorAlgebraRecovery.md),
[`AffinePointBaseChangeSmooth`](../AffinePointBaseChangeSmooth.md) (points of a base change),
[`AffineWeilEmbeddingProductMaps`](../AffineWeilEmbeddingProductMaps.md) (affineness of a base
change), [`AffinePointComparison`](../AffinePointComparison.md) (group schemes from natural
isomorphisms of affine points) and [`SimplyConnected.Basic`](../SimplyConnected/Basic.md).

## Main results

- `exists_baseChange_iso_of_weilRestriction_iso hR hred hsimple hred'' hsimple'' Φ`. Assume
  `hR : WeilFactorIdempotentRigidityStatement.{u}`. Let `B`, `B''` be finite, projective, étale
  `A`-algebras, and let `G`, `G''` be affine group schemes, locally of finite type, over
  `Spec B`, `Spec B''`. Assume both are reductive with almost simple geometric fibres. Then
  every isomorphism `Φ : R_{B/A}(G) ≅ R_{B''/A}(G'')` gives some `α : B'' ≃ₐ[A] B` and an
  isomorphism `(GroupScheme.baseChange (Spec.map α)).obj G'' ≅ G`.
- `affineSimplyConnectedWeilRestriction_uniqueness_of_rigidity hR A G`: the uniqueness
  conjunct of
  [`AffineSimplyConnectedWeilRestrictionStatement`](AffineSimplyConnectedWeilRestrictionStatement.md),
  verbatim, for the given `A` and `G`. Its hypotheses on `G` are not used; the iso
  `R_{B/A}(G') ≅ R_{B''/A}(G'')` is the composite of the two given isomorphisms with `G`.
  Simple connectedness of the fibres is not used either.
- `comparisonIso` (definition): the isomorphism `G''_α ≅ G` itself, for the `α` and the
  compatibility `hα` from `exists_algEquiv_transfer`.

So the uniqueness clause of the target statement follows formally from the derived statement
[`WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md), which
remains to be proved.

## Provenance and route

Provenance: derived. This is a formal deduction, not taken from a source. It replaces the
strictly henselian, maximal-torus argument of Conrad, *Reductive group schemes*,
Proposition 6.4.4, proof pp.232–233 (registered as `conrad-2014-reductive-group-schemes`), by
an argument with idempotents over all base changes `T`, which needs no étale localization.

1. `exists_algEquiv_transfer` (previous module) gives `α : B'' ≃ B` such that `Φ` transfers
   graph idempotents of `φ : B → T` to graph idempotents of `φ ∘ α`.
2. For a `B`-algebra `X`, let `resA X` be `X` as an `A`-algebra (`resA`, via
   `Algebra.compHom`), `structureMap A X : B → resA X`, and `graphIdem A X` its graph
   idempotent. The multiplication `mulMap A X : B ⊗ X → X` is surjective with kernel
   `(1 - graphIdem)` (`mulMap_surjective`, `ker_mulMap`). By
   `IdempotentPoints.factorEquiv`, `G(X)` is the subgroup of `G(B ⊗ X) = R_{B/A}(G)(X)`
   trivial on the `(1 - graphIdem)`-component (`factorEquivX`). This gives natural
   transformations `embNat : G(X) → R_{B/A}(G)(X)` and `projNat : R_{B/A}(G)(X) → G(X)`, with
   `projNat ∘ embNat = id` (`embNat_projNat`, `projNat_embNat_apply`) and `embNat ∘ projNat = id`
   on the factor (`embNat_projNat_of_snd`).
3. `snd_transfer_of_snd`: `Φ` maps points in the `e`-factor to points in the
   `transfer e`-factor, because `Φ ∘ factorProjection e = factorProjection (transfer e) ∘ Φ`.
4. For `X` regarded as a `B''`-algebra through `α` (`resAlpha α`), the two `A`-structures on
   `X` agree up to the identity map (`resIso`). The transfer of `graphIdem A X` is the graph
   idempotent of the `B''`-structure (`graphIdem_transfer`, `graphIdem_transfer_inv`).
5. Points of `G''_α` over `X` are points of `G''` over `X` through `α` (`bcEquiv`, `bcNat`,
   `bcIso`, from `affinePointsBaseChangeMulEquiv`).
6. `fwdNat = embNat ≫ Φ ≫ resIso ≫ projNat'' ≫ bcIso` and the reverse `bwdNat` are inverse
   (`fwdNat_bwdNat`, `bwdNat_fwdNat`). `AffinePointComparison.iso` turns this natural
   isomorphism of affine points into `comparisonIso`.

Auxiliary declarations: `resA`, `structureMap`, `mulMap` (+ `mulMap_apply`,
`mulMap_surjective`, `ker_mulMap`), `graphIdem`, `graphIdem_spec`, `graphIdem_map`,
`snd_map_eq_one`, `mulMap_comp_lTensor`, `factorEquivX`, `factorEquivX_symm_natural`,
`embNat`, `mulMap_points_natural`, `projNat`, `embNat_projNat`, `embNat_projNat_of_snd`,
`projNat_embNat_apply`, `baseIdem_id`, `snd_transfer_of_snd`, `resAlpha`, `resIsoHom`,
`resIsoInv`, `resIso`, `resIso_hom_app_hom`, `baseChangeAlpha`, `bcEquiv`,
`bcEquiv_symm_left`, `bcNat`, `bcNatInv`, `bcIso`, `apfMap`, `graphIdem_transfer`,
`graphIdem_transfer_inv`, `fwdNat`, `bwdNat`, `affinePointMap_inv_hom`, `fwdNat_bwdNat`,
`bwdNat_fwdNat`.

## Scope

The module does not prove the rigidity statement. It does not state that `(α, f)` is unique
or functorial in `Φ`, though the construction of `α` depends only on `Φ`.
