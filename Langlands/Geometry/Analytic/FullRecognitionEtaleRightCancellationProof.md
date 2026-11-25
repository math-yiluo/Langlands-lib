# Strong étale right cancellation over all affinoid pieces: proof

Lean module: `Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationProof`,
namespace `Langlands.Analytic.AffinoidAtlasPresentation.StrongHom`.

## Statement

```
theorem Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.etaleRightCancellation
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    EtaleRightCancellationStatement.{u, v, w} K
```

The type is exactly the published proposition
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.EtaleRightCancellationStatement.{u, v, w} K`
of the module `Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationStatement`,
for every complete ultrametric normed field `K : Type u`, with the three
universes `u` (the field), `v` (the spaces) and `w` (the atlas indices)
independent, and no further hypothesis. Unfolded, it reads:

```
∀ (A B C : AffinoidAtlasPresentation.{u, v, w} K)
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
  (g' : StrongHom B.saturatedPresentation C.saturatedPresentation),
  g'.IsEtaleAllPieces →
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces →
    g.IsEtaleAllPieces
```

In words: for two composable strong maps `g : A → B` and `g' : B → C` between
the saturated presentations of affinoid atlas presentations over `K`, if `g'`
and the saturated composite are étale over all recognized affinoid pieces,
then so is `g`. Quasifiniteness of `g` is not assumed.

## Proof

The Lean proof is the single application

```
etaleRightCancellation_of_finiteOver (finiteOverRightCancellation K)
```

of `etaleRightCancellation_of_finiteOver` (module
`Geometry.Analytic.AffinoidEtalePointCancellation`), which derives the
statement from `FiniteOverRightCancellationStatement.{u, v, w} K`, to
`finiteOverRightCancellation K` (module
`Geometry.Analytic.FullRecognitionFiniteRightCancellationProof`), proved
without hypotheses: two finite maps over the same open base make the
intervening strong map finite.

Inside the reduction, finite right cancellation produces the finite
neighbourhoods of `g`, and étaleness is cancelled pointwise on the recognized
pieces; the details are on the page of
`Geometry.Analytic.AffinoidEtalePointCancellation`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.etaleRightCancellation`.

## Literature

V. G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
Publ. Math. IHÉS 78 (1993), §3.3, Corollary 3.3.9, printed p. 63: for
quasifinite morphisms `ψ : Z → Y` and `φ : Y → X` with `φψ` étale and `φ`
unramified, `ψ` is étale. The Lean statement is the fixed-base cancellation
with the Library's all-pieces predicates and without the quasifiniteness of
the first map, as described on the statement's page.
