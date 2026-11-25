# Statement: stability of quasi-étale morphisms

This module states, without proof, the stability properties of quasi-étale
morphisms in Berkovich 1994, Lemma 3.1. It has four Prop-valued definitions in
the namespace `Langlands.Analytic.SaturatedAtlasPresentation`. Each takes a
complete ultrametric normed field `K : Type u` as an explicit argument and is
about the localized category of analytic spaces
`LocalizedCategory.{u, v, v} (K := K)`. Here `quasiEtale` is the Library
predicate of the module `QuasiEtaleSite`. It holds for arrows isomorphic in the
arrow category to the localization of a strong map `g` with `IsQuasiEtale g`:
each point of the source has a neighbourhood that is a finite union of atlas
charts, and each chart is identified, compatibly with the map, with an affinoid
domain of a space étale over the target.

## The statements

1. `QuasiEtaleCompStatement K` is the Mathlib class
   `MorphismProperty.IsStableUnderComposition quasiEtale`. If `f : A ⟶ B` and
   `g : B ⟶ C` are quasi-étale, then `f ≫ g` is quasi-étale.
2. `QuasiEtaleBaseChangeStatement K` is the Mathlib class
   `MorphismProperty.IsStableUnderBaseChange quasiEtale`. Take a square
   `IsPullback f' g' g f` with `f' : Y' ⟶ Y`, `g' : Y' ⟶ X`, `g : Y ⟶ S` and
   `f : X ⟶ S`. If `g` is quasi-étale, then `g'` is quasi-étale. Here
   `IsPullback` is the categorical pullback property in the localized category:
   it holds against every localized analytic test object. The statement
   applies to every pullback square. It does not assert that pullbacks exist.
3. `QuasiEtaleOverMorphismStatement K` is the Mathlib class
   `MorphismProperty.HasOfPostcompProperty quasiEtale quasiEtale`. If
   `g : Y ⟶ X` and `f ≫ g : Z ⟶ X` are quasi-étale, then `f : Z ⟶ Y` is
   quasi-étale. So every morphism over `X` between objects quasi-étale over
   `X` is quasi-étale.
4. `QuasiEtaleStabilityStatement K` is the conjunction of the three
   statements above, in this order.

No Hausdorff, compactness or smallness hypothesis is imposed on any object.
The universe parameters are those of the localized category: `u` for the field
and `v` for the spaces and atlas indices.

## Original source

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed
p.544 (PDF p.6), Lemma 3.1:

> (i) Quasi-étale morphisms are preserved under compositions, under any base
> change functor and under any ground field extension functor.
> (ii) If Y and Z are quasi-étale over X, then any X-morphism Z → Y is
> quasi-étale.

The definition of quasi-étale morphisms is on printed p.543 (PDF p.5). The
paper works with k-analytic spaces in the sense of Berkovich 1990 and 1993,
over any non-Archimedean field, without a Hausdorff convention in §3.

Statements 1 and 2 are the composition and base-change clauses of (i).
Statement 3 is (ii). In Berkovich, a base change functor sends `Y → X` to the
fibre product `Y ×_X X' → X'`. Statement 2 transcribes this as the projection
of any categorical pullback square in the Library's localized category.

The ground field extension clause of (i) is omitted: the Library has no ground
field extension functor on its localized category. These statements are its
counterpart in the Library's vocabulary: `LocalizedCategory`, `quasiEtale`,
`IsPullback` and the Mathlib morphism-property classes take the place of
Berkovich's category of k-analytic spaces, his quasi-étale morphisms and his
fibre products.

Berkovich's proof is one line: "All the statements easily follow from the
corresponding properties of étale morphisms and Theorem 3.4.1 from [Ber2]",
where [Ber2] is Berkovich 1993 (`berkovich-1993-etale-cohomology`). In the
Library, étale composition is the instance in `LocalizedEtaleComposition`.
Étale right cancellation and étale base change are the statements
`LocalizedEtaleStabilityStatement`, `LocalizedEtalePullbackStatement` and
`EtaleBaseChangeStatement`, proved in `EtalePointwiseLifting.LocalizedStability`,
`LocalizedEtalePullbackProof` and `EtaleBaseChangeProof`.

## Use

The three statements are the quasi-étale stability properties that a site
pullback in `QuasiEtaleSite X` needs: a site arrow `f : U ⟶ B` has a
quasi-étale underlying arrow by statement 3. The projection of a pullback
parallel to it is quasi-étale by statement 2. The composite structure map to
`X` is quasi-étale by statement 1. This is the route of the reduction of
`CompactQuasiEtalePullbacksStatement`.

## Scope

This is a statement module: nothing is proved here.
