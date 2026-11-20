# Étale base change along glued fibre products: conditional reduction

This module reduces the Library proposition
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleBaseChangeStatement` to two
other Library propositions:

- `PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement.{u}`, which
  says that finite Banach affinoid algebras descend effectively along finite
  full-domain covers (Kiehl's theorem in the Library's formulation);
- `FibreProductPullbackStatement.{u}`, which says that the glued fibre product
  `fibreProduct f g`, together with `fibreProductFst f g` and
  `fibreProductSnd f g`, is a pullback of `f` and `g` in the localized category
  `LocalizedCategory`.

Both appear as explicit hypotheses. This module proves neither of them, and it
does not prove `EtaleBaseChangeStatement` unconditionally.

## Declarations

### `etale_snd_of_isPullback`

Let `h : IsPullback p q f g` and `h' : IsPullback p' q' f g` be two pullback
squares of the same cospan `f : A ⟶ X`, `g : B ⟶ X` in
`LocalizedCategory.{u, v, v} K`. If `etale q`, then `etale q'`.

Proof: Mathlib's `IsPullback.isoIsPullback` gives an isomorphism
`e : P' ≅ P` between the top-left corners. By `IsPullback.isoIsPullback_hom_snd`
it satisfies `e.hom ≫ q = q'`. The property `etale` respects isomorphisms
(the instance `RespectsIso` in `EtaleSite`). So
`MorphismProperty.cancel_left_of_respectsIso` carries `etale q` to
`etale (e.hom ≫ q)`.

### `etaleBaseChange_of_localizedEtalePullback`

Hypotheses:

- `hpull : FibreProductPullbackStatement.{u}`;
- `hetale`: for every complete ultrametric normed field `K : Type u`,
  `LocalizedEtalePullbackStatement.{u, u} K`. This proposition says that
  every cospan `f, g` in `LocalizedCategory.{u, u, u} K` with `etale f` has a
  pullback square `IsPullback p q f g` with `etale q`.

Conclusion: `EtaleBaseChangeStatement.{u}`.

Proof: take `K`, the Hausdorff saturated presentations `X`, `Y`, `S` in
`SaturatedAtlasPresentation.{u, u, u} K`, the strong maps `f : X ⟶ S` and
`g : Y ⟶ S`, and `hf : etale (localizationFunctor.map f)`. Apply `hetale K` to
`localizationFunctor.map f` and `localizationFunctor.map g`. This gives some
pullback square with an étale second projection `q`. `hpull K X Y S f g` says
that the square of the glued fibre product is also a pullback square of the
same cospan. `etale_snd_of_isPullback` then transfers `etale q` to
`etale (localizationFunctor.map (fibreProductSnd f g))`.

The universe of the localized category in `hetale` is `{u, u}`, because the
target statement fixes field, space and index universes all equal to `u`.

### `etaleBaseChange_of_descent`

Hypotheses:

- `hdesc : PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement.{u}`;
- `hpull : FibreProductPullbackStatement.{u}`.

Conclusion: `EtaleBaseChangeStatement.{u}`.

It is declared with `def` (its type is a proposition, and the linter
`linter.defProp` is switched off for this declaration), so that it can be
recorded as a supporting definition artifact.

Proof: apply `etaleBaseChange_of_localizedEtalePullback` with `hpull`. For each
`K`, the hypothesis `hetale` comes from three published Library results:

1. `localizedEtalePullback_of_targetLocality_and_finitePieces`
   (`ConditionalLocalizedEtalePullback`). It proves
   `LocalizedEtalePullbackStatement.{u, v} K` from
   `FiniteOverTargetLocalityStatement.{u, v, v} K` and
   `FinitePiecesEtaleAllPiecesStatement.{u, v, v} K`.
2. `AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent`
   (`FullRecognitionFiniteTargetLocalityOfDescent`). It proves the first input
   from `hdesc`.
3. `AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces`
   (`FinitePiecesEtaleAllPiecesProof`). It is the unconditional proof of the
   second input.

## Status of the hypotheses

- A proof of `FiniteAffinoidAlgebraDescentStatement` is the proof candidate
  `ee637edc-ef7e-490a-9c08-af4454387d30` of Task 7635. Its review approved it
  and it was waiting for integration when this module was written. It was not
  yet in the Library.
- `FibreProductPullbackStatement` is the target of Task 5642. When this module
  was written it had no published proof and no candidate.

Once both have published proofs, applying `etaleBaseChange_of_descent` to them
proves `EtaleBaseChangeStatement`.

## Provenance and route

The statement being reduced is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993), Corollary 3.3.8,
printed p. 63 (PDF p. 60): étale morphisms are preserved under any base change
functor. Literature `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The route here is internal and differs from Berkovich's. Berkovich derives the
corollary from the pointwise description of étale quasifinite morphisms
(Corollary 3.3.6 and Proposition 3.3.7, printed p. 63, and Corollary 3.2.6,
printed p. 59). This module does not use that argument and does not prove
anything about the affinoid pieces of `fibreProductSnd f g`. It only compares
two pullback squares of the same cospan. All of the geometry is in the Library
results that `etaleBaseChange_of_descent` cites. They build an actual pullback
with an étale second leg along every étale morphism of the localized category.
Two pullbacks of one cospan are isomorphic over the second leg, and `etale`
respects isomorphisms. So the glued fibre product inherits étaleness once it is
known to be a pullback.
