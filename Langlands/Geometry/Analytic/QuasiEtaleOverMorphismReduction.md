# Morphisms over `X` between quasi-étale spaces: reduction to pointed local factorizations

Module `Langlands.Geometry.Analytic.QuasiEtaleOverMorphismReduction`. Everything is in the
namespace `Langlands.Analytic.SaturatedAtlasPresentation`. `K` is a complete ultrametric
normed field, and all objects lie in `LocalizedCategory.{u, v, v} (K := K)` unless a result
says otherwise.

The module proves Berkovich's Lemma 3.1(ii) (*Vanishing cycles for formal schemes*, Invent.
Math. 115 (1994), §3, printed p.544): if `g : Y ⟶ X` and `f ≫ g : Z ⟶ X` are quasi-étale,
then so is `f : Z ⟶ Y`. The proof is conditional on one premise, which the module does not
prove. Berkovich's proof is the single remark that the lemma follows from properties of étale
morphisms and from Theorem 3.4.1 of his 1993 paper. The Lean route below is a direct graph
argument and does not use that theorem.

## The premise

`quasiEtaleOverMorphism_of_localDomainFactorizations` takes as hypothesis

`∀ {U X : LocalizedCategory.{u, v, v} (K := K)} (f : U ⟶ X), quasiEtale f → HasLocalDomainEtaleFactorizations f`.

`HasLocalDomainEtaleFactorizations` (module `QuasiEtaleDomainLocality`) asks, at every source
point, for finitely many analytic domains that **contain the point**, whose union is a
neighbourhood of it, and on each of which the restricted arrow has a domain–étale
factorization (`HasDomainEtaleFactorization`). The hypothesis is the body of the proposition
`QuasiEtaleLocalDomainFactorizationsStatement` (module
`QuasiEtaleLocalDomainFactorizationsStatement`). It is written out here rather than imported.
Once that statement is proved, applying this reduction to the proof yields the exact
`QuasiEtaleOverMorphismStatement.{u, v} K`.

The premise is unproved in the Library. The Library proves it for a Hausdorff source
(`hasLocalDomainEtaleFactorizations_of_quasiEtale`) and proves the converse in general
(`HasLocalDomainEtaleFactorizations.quasiEtale`). The Library's `IsQuasiEtaleAt` follows
Berkovich's 1994 definition (printed p.543): its charts need not contain the point.

Without a Hausdorff hypothesis the premise cannot be replaced by direct manipulation of such
families. Consider two closed discs glued along an open subset, with a doubled boundary
point. Take `Z` to be the first disc, `Y = X` to be the glued space, `f` the inclusion and
`g = 𝟙`. Preimages under `f` of a nonpointed chart family of `g` at the doubled point include
an open annulus. No finite family of compact charts inside the preimages is then a
neighbourhood of the point.

## Results

- `IsAnalyticDomainEmbedding.of_comp_mono`: if `c ≫ m` is an analytic-domain embedding and
  `m` is a monomorphism, then `c` is an analytic-domain embedding. The square with sides `𝟙`,
  `c`, `c ≫ m` and `m` is a pullback because `m` is a monomorphism, and
  `IsAnalyticDomainEmbedding.of_isPullback` (module `QuasiEtaleDiagonalLocal`) applies.
- `IsAnalyticDomainEmbedding.mono`: analytic-domain embeddings are monomorphisms (an
  isomorphism followed by a domain inclusion, `domainι_mono`).
- A private lemma `etale_of_isPullback_localized`: in every pullback square along an étale
  arrow, the parallel projection is étale. This is the Library's
  `localizedEtalePullbackBaseChange` (module `LocalizedEtalePullbackProof`) combined with
  `etale_snd_of_isPullback` (module `EtaleBaseChangeReduction`).
- `isAnalyticDomainEmbedding_graph` (local graph lemma). The data are:
  - an étale `w : W ⟶ X` and a pullback `P` of `w` along `g : Y ⟶ X`, with projections
    `pW`, `pY`;
  - an analytic-domain embedding `a : T ⟶ W`, and `k : T ⟶ D` with `a ≫ w = (k ≫ m) ≫ g`;
  - an analytic-domain embedding `m : D ⟶ Y`, and an analytic-domain embedding `b : D ⟶ U`
    with `m ≫ g = b ≫ u` for an étale `u : U ⟶ X`.

  Under these hypotheses the graph `T ⟶ P` of `(a, k ≫ m)` is an analytic-domain embedding.
- `HasDomainEtaleFactorization.of_comp_of_factor` (local graph factorization). Suppose `h ≫ g`
  has a domain–étale factorization and `h = k ≫ m`, where `m` is an analytic-domain embedding
  and `m ≫ g` has a domain–étale factorization. Then `h` has a domain–étale factorization:
  the graph of `h` into the pullback `P` of the étale envelope `w` of `h ≫ g` along `g`,
  followed by the projection `pY`, which is étale by base change.
- `quasiEtaleOverMorphism_of_localDomainFactorizations`: the premise above implies
  `QuasiEtaleOverMorphismStatement.{u, v} K`. It is declared with `def` (its type is a
  proposition).

## Proof of the local graph lemma

Every pullback used is one supplied by `localizedEtalePullback` along an étale arrow. Write
`ε := (a, k ≫ b) : T ⟶ Q`, where `Q = W ×_X U`. Both projections of `Q` are étale.

1. Let `R = Q ×_W T`, the pullback of `Q ⟶ W` along `a`. Its projection `R ⟶ T` is étale, and
   `s = (ε, 𝟙) : T ⟶ R` is a section of it. By `localizedEtaleSectionsOpen` (module
   `EtaleSectionsOpen`), `s` is an open immersion, hence an analytic-domain embedding onto an
   open domain. The projection `R ⟶ Q` is the base change of `a`, hence an analytic-domain
   embedding by `IsAnalyticDomainEmbedding.of_isPullback`. So `ε = s ≫ (R ⟶ Q)` is an
   analytic-domain embedding (`IsAnalyticDomainEmbedding.comp`).
2. Let `S = Q ×_U D`, the pullback of `Q ⟶ U` along `b`. Its projection `S ⟶ Q` is the base
   change of `b`, hence an analytic-domain embedding and a monomorphism. `ε` factors as
   `ε' ≫ (S ⟶ Q)` with `ε' = (ε, k)`, so `ε'` is an analytic-domain embedding by
   `of_comp_mono`.
3. The arrow `t : S ⟶ P` induced by `S ⟶ Q ⟶ W` and `S ⟶ D ⟶ Y` fits into a pullback square
   with `m` and `pY`. The square is checked directly from the universal properties of `P`, `Q`
   and `S`. So `t` is the base change of `m`, hence an analytic-domain embedding.
4. Both projections of `P` agree on the graph and on `ε' ≫ t`, so the two arrows are equal.
   The graph is therefore an analytic-domain embedding.

## Proof of the reduction

The target is `MorphismProperty.HasOfPostcompProperty quasiEtale quasiEtale`. Let `g` and
`f ≫ g` be quasi-étale, and let `z` be a point of `Z`. By
`HasLocalDomainEtaleFactorizations.quasiEtale` it suffices to give pointed local
factorizations of `f` at `z`.

The premise, applied to `f ≫ g` at `z` and to `g` at the image of `z`, gives two finite
families of analytic domains `E ∋ z` of `Z` and `D ∋ f(z)` of `Y`. Both are pointed and have
neighbourhood unions. The required family is the finite family of domains
`E ⊓ domainPreimage f D`. Each of them contains `z`. Their union contains the intersection of
the first union with the preimage of the second, which is a neighbourhood of `z` by
continuity.

On `T = E ⊓ domainPreimage f D`, two facts hold:

- `domainι T ≫ f ≫ g` has a domain–étale factorization, by restricting that of `E`
  (`HasDomainEtaleFactorization.of_domain_le`);
- `domainι T ≫ f` factors as `k ≫ domainι Y D`, with `k` the order map into
  `domainPreimage f D` followed by `domainPreimageMap f D`.

`HasDomainEtaleFactorization.of_comp_of_factor` then gives the factorization of
`domainι T ≫ f`.

## Scope

Proved: the reduction above, with standard axioms only. It uses no Hausdorff, compactness or
smallness hypothesis and no unproved Library proposition other than the explicit premise. In
particular it does not use `LocalizedEtaleStabilityStatement`, quasi-étale composition or
base change, or strong étale right cancellation.

Not proved: the premise. Nor does the module prove
`QuasiEtaleOverMorphismStatement` itself.
