# Proof: monomorphisms out of reductive group schemes are closed immersions

`Langlands.GroupScheme.reductiveMonomorphismClosedImmersion.{u}` proves the Library proposition
`Langlands.GroupScheme.ReductiveMonomorphismClosedImmersionStatement.{u}`, imported from
[`Reductive.MonomorphismClosedImmersionStatement`](MonomorphismClosedImmersionStatement.md), in
every universe `u` and with no additional hypotheses.

```lean
theorem reductiveMonomorphismClosedImmersion :
    ReductiveMonomorphismClosedImmersionStatement.{u}
```

## Statement proved

Let `S` be an arbitrary scheme, `G` a reductive group scheme over `S` (`IsReductive G`), and
`G'` an `S`-group scheme whose structure morphism is separated, locally of finite presentation
and quasi-compact. Every homomorphism `f : G ⟶ G'` whose underlying morphism of schemes is a
monomorphism has a closed immersion as its underlying morphism of schemes. This is the first
sentence of Theorem 5.3.5 of Conrad, *Reductive group schemes* (2014); the statement page records
the correspondence between the source and the Lean encoding.

## Proof

The proof term is

```lean
ReductiveMonomorphismDvrReduction.generalCase_of_dvrCase
  (DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase
    dvrGenericAffineness ReductiveGenericClosure.dvrMatrixCase)
```

It composes three reductions and two proved inputs from the Library, all in the same universe
`u`.

1. **From an arbitrary base to discrete valuation rings.**
   `ReductiveMonomorphismDvrReduction.generalCase_of_dvrCase` (module
   [`Reductive.MonomorphismDvrReduction`](MonomorphismDvrReduction.md)) has type
   `ReductiveMonomorphismValuativeReduction.DvrCase.{u} →
   ReductiveMonomorphismClosedImmersionStatement.{u}`. It restricts to affine charts of the
   base and descends the homomorphism to a model over a finitely generated coefficient ring
   (noetherian approximation). Over a locally noetherian base, it then uses the valuative
   criterion over discrete valuation rings
   (`ReductiveMonomorphismValuativeReduction.locallyNoetherianCase_of_dvrCase`): a universally
   closed monomorphism is proper, hence a closed immersion. `DvrCase` is the same assertion over
   `Spec R` for a discrete valuation ring `R`.
2. **From discrete valuation rings to the matrix case.**
   `DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase` (module
   [`Reductive.DvrPidLinearEmbeddingReduction`](DvrPidLinearEmbeddingReduction.md)) has type
   `DvrGenericAffinenessStatement.{u} → ReductiveDvrMatrixMonomorphismStatement.{u} →
   ReductiveMonomorphismValuativeReduction.DvrCase.{u}`. Over a discrete valuation ring, it
   replaces the target by the schematic closure of the generic image of `f`. That closure is
   flat, separated and of finite type, with affine generic fibre, so Raynaud's criterion makes
   it affine (`DvrAffineClosureReduction.dvrCase_of_flatAffineCase`). It then embeds this flat
   affine target as a closed subgroup of some `GL_N`
   (`IntegralLinearEmbedding.exists_isClosedSubgroup_of_dvr`). This reduces the claim to
   monomorphisms from a reductive group into `GL_N`, and closed immersions cancel against the
   separated closed embedding.
3. **Raynaud's affineness criterion.** `Langlands.GroupScheme.dvrGenericAffineness` (module
   [`DvrGenericAffinenessProof`](../DvrGenericAffinenessProof.md)) proves
   `DvrGenericAffinenessStatement.{u}`. A flat, quasi-compact group scheme locally of finite type
   over a discrete valuation ring, with affine generic fibre, is affine if and only if it is
   separated.
4. **The matrix case.** `Langlands.GroupScheme.ReductiveGenericClosure.dvrMatrixCase` (module
   [`Reductive.DvrGenericClosureIsomorphism`](DvrGenericClosureIsomorphism.md)) proves
   `ReductiveDvrMatrixMonomorphismStatement.{u}`. Over a discrete valuation ring, a homomorphism
   from a reductive group to `GL_N` that is a monomorphism of schemes is a closed immersion. It
   factors the homomorphism through the schematic closure of its generic image and shows that
   the factor is an isomorphism. The homomorphism is first an immersion
   (`ReductiveImmersion.isImmersion_of_mono`, over an arbitrary base): étale-locally the source
   has a split maximal torus whose image is closed, and for a regular cocharacter of that torus
   the dynamic triple cells (open in the target, with closed cell factor) give the immersion.
   Hence the factor through the closure is an open immersion
   (`ReductiveGenericClosure.factor_isOpenImmersion`), and it is an isomorphism on generic
   fibres. The closure is smooth (`ReductiveGenericClosure.closure_smooth`), so the open-subgroup
   criterion over a discrete valuation ring (`EtaleOpenGenericIsomorphism.isIso_of_dvr`) makes
   the factor an isomorphism.

Items 3 and 4 discharge the two premises of item 2, and item 2 discharges the premise of item 1.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source proof

Conrad's proof (pp.166–170) has the same outline. Limit arguments reduce to a noetherian base
and the valuative criterion to a discrete valuation ring. The schematic closure of the generic
fibre, affine by Raynaud, embeds in `GL_n` (p.166). Both arguments then use open cells to show
that the homomorphism is an immersion, and finish by identifying the source with the schematic
closure of its generic image over a discrete valuation ring. They differ in how they obtain the
immersion. Conrad proves that the homomorphism is a closed immersion over the open cell of the
target, using the root-group filtrations (Lemmas 5.3.6–5.3.8, pp.167–169), and covers the
source by Weyl translates of its open cell. The Library obtains the immersion from closed images
of split maximal tori and dynamic triple cells, as described in item 4. For the last step,
Conrad shows on p.170 that the closure is smooth and contains the source as an open subgroup,
and applies his Proposition 3.1.12. The Library applies
`EtaleOpenGenericIsomorphism.isIso_of_dvr` to the open factor through the smooth closure.

## Declarations used

- `ReductiveMonomorphismClosedImmersionStatement`
  (`Langlands.GroupScheme.Reductive.MonomorphismClosedImmersionStatement`);
- `ReductiveMonomorphismDvrReduction.generalCase_of_dvrCase`
  (`Langlands.GroupScheme.Reductive.MonomorphismDvrReduction`);
- `DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase`
  (`Langlands.GroupScheme.Reductive.DvrPidLinearEmbeddingReduction`);
- `dvrGenericAffineness` (`Langlands.GroupScheme.DvrGenericAffinenessProof`);
- `ReductiveGenericClosure.dvrMatrixCase`
  (`Langlands.GroupScheme.Reductive.DvrGenericClosureIsomorphism`).

## Sources

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas et
Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`; one-based PDF pages, which
agree with the printed pages): Theorem 5.3.5, p.165, and its proof, pp.166–170, with
Proposition 3.1.12, pp.89–90. Raynaud's
criterion is Proposition 3.1 of Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive group schemes*,
author preprint p.5, registered as `prasad-yu-2006-quasi-reductive-author-preprint`. The pages
of the imported modules give the sources of the individual steps.
