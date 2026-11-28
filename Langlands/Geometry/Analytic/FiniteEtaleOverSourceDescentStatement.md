# Descent of finite étaleness along a finite étale surjection

This module contains only the Prop-valued definition
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteEtaleOverSourceDescentStatement`.
It says that a map is finite étale over an open set once its composite with a
finite étale surjection onto that set is finite étale. The file states the
proposition and does not prove it.

## Exact statement

`FiniteEtaleOverSourceDescentStatement.{u, v, w} : Prop` asserts the following.
Let `K : Type u` be a field with `NormedField K`, `IsUltrametricDist K` and
`CompleteSpace K`. Let `A`, `B`, `C` be analytic presentations
(`AffinoidAtlasPresentation.{u, v, w} K`). Let
`q : StrongHom A.saturatedPresentation B.saturatedPresentation` and
`f : StrongHom B.saturatedPresentation C.saturatedPresentation` be strong maps
between their saturated presentations. Let `E ⊆ A.space`, `V ⊆ B.space` and
`T ⊆ C.space` be sets satisfying
1. `E`, `V` and `T` are open;
2. `V`, with the subspace topology, is Hausdorff (`T2Space V`);
3. `q` maps `E` onto `V`: `q.baseMap '' E = V`;
4. `q` is finite étale from `E` to `V` (`q.IsFiniteEtaleOver E V`);
5. the composite strong map
   `q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains`,
   whose base map is `f.baseMap ∘ q.baseMap`, is finite étale from `E` to `T`.

Then `f` is finite étale from `V` to `T` (`f.IsFiniteEtaleOver V T`).

- `IsFiniteEtaleOver` is defined in the module
  `Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms`.
  `g.IsFiniteEtaleOver V U` says that `g` maps `V` into `U`, and that for every
  recognized affinoid `W` of the target's saturated atlas with locus in `U`,
  the set `V ∩ g⁻¹(W)` is the locus of a recognized affinoid `V'` of the
  source's saturated atlas. Moreover the bounded algebra map
  `g.fullRecognitionPairs.pullback V' W _` is a finite Banach map
  (`IsFiniteBanach`) and is algebraically finite étale
  (`AlgebraicallyFiniteEtale`). This is Berkovich's notion of a finite morphism
  (the preimage of every affinoid domain is an affinoid domain, finite over
  it) restricted to the open subspaces `V` and `U`, with finite étale affinoid
  algebra maps.
- Hypotheses 3 and 4 together say that `E` is the source of a finite étale
  surjection onto `V`. In particular, for every recognized affinoid `H` with
  locus in `V`, the preimage `E ∩ q⁻¹(H)` is a recognized affinoid that maps
  onto `H`.
- The conclusion asks for a recognized preimage `V ∩ f⁻¹(W)` for **every**
  recognized affinoid `W` with locus in `T`. Its recognition is not a
  hypothesis.
- The field may be trivially normed. The universes of the field (`u`), of the
  spaces (`v`) and of the atlas indices (`w`) are independent. The ambient
  spaces need not be Hausdorff; only the open set `V` is assumed Hausdorff.

## Original sources

Conrad and Temkin, *Non-archimedean analytification of algebraic spaces*,
J. Algebraic Geom. 18 (2009), author-hosted preprint, registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`
(printed page = PDF page):
- Lemma 3.2.1, printed pp.15–16: for a finite étale surjective map
  `f : U → X` of rigid spaces, `X` is affinoid if and only if `U` is affinoid.
  The paragraph after the statement (p.15) says that the proof carries over
  verbatim to affinoid `k`-analytic spaces that need not be strictly
  `k`-analytic: for a `k`-affinoid algebra `A` with a continuous action of a
  finite group `G`, the subalgebra `A^G` is `k`-affinoid and `A` is finite and
  admissible over it (they cite Berkovich 1990, 2.1.14(ii)).
- Theorem 4.1.2, printed pp.18–19: for a finite étale map `f : X' → X` of
  `k`-analytic spaces and a quasi-compact analytic subdomain `V' ⊆ X'`, the
  image `f(V')` is a finite union of affinoid domains of `X`. The proof first
  reduces to a Hausdorff target. In its last step `V'` is the full preimage of
  `f(V')`, so that `V' → f(V')` is finite, and Lemma 3.2.1 shows that `f(V')`
  is affinoid. The convention of §4.1 (p.17) allows `k` to have trivial
  absolute value.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`
(printed page = PDF page + 3):
- Lemma 1.3.7 and the definition after it, printed pp.27–28: a morphism is
  finite if the preimage of every affinoid domain is an affinoid domain finite
  over it. It suffices to check this on finitely many affinoid domains around
  each point of the target.
- Definition 3.3.4, printed p.63: a quasifinite morphism is étale if it is
  unramified and flat.

## Why the statement is expected to hold

Write `c` for the composite. Fix a recognized affinoid `W` with locus in `T`.
The finite étale hypothesis on `c` makes `P = E ∩ c⁻¹(W)` a recognized
affinoid of `A`, finite étale over `W`. Put `H = V ∩ f⁻¹(W)`. It is the
preimage of the affinoid domain `W` under `f` restricted to `V`, hence an
analytic domain of `V`. Since `q` maps `E` onto `V`, `H = q(P)`, and
`P = E ∩ q⁻¹(H)` is the full preimage of `H` in `E`. Hence `q` restricts to a
finite étale surjection `P → H`, the base change of `E → V` along `H ⊆ V`. As
`P` is affinoid and `V` is Hausdorff, Lemma 3.2.1 of Conrad–Temkin (in its
`k`-analytic form) shows that `H` is affinoid. Theorem 4.1.2 of the same paper
describes the same situation, for images of quasi-compact domains under finite
étale maps.

Given an affinoid `H` in this position, the maps of affinoid algebras
`𝒲 → ℋ → 𝒫` have `ℋ → 𝒫` and `𝒲 → 𝒫` finite étale, with surjective map of
spectra `P → H`. The Library proves that then `𝒲 → ℋ` is finite Banach and
algebraically finite étale, as
`Langlands.Analytic.BoundedAlgHom.finiteBanach_etale_of_finiteEtale_comp`
(module `Langlands.Geometry.Analytic.FiniteEtaleSourcePieces`). The theorem
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsFiniteEtaleOver.of_comp_of_recognizedImages`
(module `Langlands.Geometry.Analytic.FiniteEtaleSourceRecognition`) packages
this step. For a cover `q` finite étale from an open set `D` to `U`, an open
`E ⊆ D` and a composite finite étale from `E` to `T`, it concludes that `f` is
finite étale from `q(E)` to `T`, provided that for every recognized `W` with
locus in `T` the set `q(E) ∩ f⁻¹(W)` is the locus of a recognized affinoid of
`B`. With `D = E` and `U = V`, the present statement thus amounts to the
recognition of `H = V ∩ f⁻¹(W)` as an affinoid of `B`'s saturated atlas, the
geometric content of Lemma 3.2.1.

## Provenance: derived

The proposition is a derived statement, not transcribed from a single theorem
of the sources. It combines Conrad–Temkin's descent of affinoids along finite
étale surjections (Lemma 3.2.1, in its `k`-analytic form) with the descent of
finite étale algebra maps through a faithfully flat finite étale map. It is
stated for Berkovich's finite morphisms (Lemma 1.3.7) between open subspaces,
in the Library's language of strong maps, recognized affinoids and
full-recognition pullbacks. The surjectivity of `q` onto `V` makes each `P` the
full preimage of `H`, the position in which Lemma 3.2.1 applies. The Hausdorff
hypothesis on `V` matches the reduction to a Hausdorff target at the start of
the proof of Theorem 4.1.2; affinoid domains are Hausdorff. The argument above
explains why the statement is expected to hold and is not a proof.

## Use

The proposition is the missing step in the pointwise argument described in
the module `Langlands.Geometry.Analytic.LocalizedEtaleSourceDescentStatement`.
That argument needs `q(E) ∩ f⁻¹(W)` to be recognized for a finite étale
cover `q` and an étale composite. When `E` is shrunk so that `q` is finite
étale from `E` onto its image `V`, this proposition gives that `f` is finite
étale from `V` to `T`.
