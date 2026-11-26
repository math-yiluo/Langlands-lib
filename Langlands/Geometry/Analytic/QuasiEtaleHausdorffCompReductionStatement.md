# Statement: composition of quasi-étale morphisms with Hausdorff sources from one premise

This module states, without proof, one proposition in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. It takes a complete
ultrametric normed field `K : Type u` as an explicit argument. All objects lie
in the localized category `LocalizedCategory.{u, v, v} (K := K)`. The
universes are those of `QuasiEtaleHausdorffCompStatement`: `u` for the field
and `v` for the spaces and atlas indices.

## The statement

`QuasiEtaleHausdorffCompReductionStatement K` is the implication

    EtaleDomainQuasiEtaleStatement K → QuasiEtaleHausdorffCompStatement K.

- `EtaleDomainQuasiEtaleStatement K` (module `QuasiEtaleCompPrerequisites`):
  let `D` be an analytic domain of `W` and `e : E ⟶ domainObj W D` an étale
  morphism into the domain. Then `e ≫ domainι W D` is quasi-étale, where
  `domainι W D` is the inclusion of the domain.
- `QuasiEtaleHausdorffCompStatement K` (module
  `QuasiEtaleHausdorffStabilityStatement`): let `f : A ⟶ B` and `g : B ⟶ C`
  be quasi-étale, and suppose `T2Space (localizedSpaceFunctor.obj A)` and
  `T2Space (localizedSpaceFunctor.obj B)`. Then `f ≫ g` is quasi-étale. No
  hypothesis is made on `C`.

Here `quasiEtale` is the Library predicate of the module `QuasiEtaleSite`.

## Original source and provenance

The statement is derived. It is the composition clause of Berkovich, *Vanishing
cycles for formal schemes*, Invent. Math. 115 (1994), registered as
`berkovich-1994-vanishing-cycles-formal-schemes`, Lemma 3.1(i) (printed
p.544, PDF p.6), restricted in two ways:

- The sources `A` and `B` are Hausdorff. These are the hypotheses of
  `QuasiEtaleHausdorffCompStatement`; the Markdown of
  `QuasiEtaleHausdorffStabilityStatement` explains why.
- One ingredient of Berkovich's one-line proof is a named premise. The proof
  reads: "All the statements easily follow from the corresponding properties
  of étale morphisms and Theorem 3.4.1 from [Ber2]". [Ber2] is Berkovich,
  *Étale cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78
  (1993), registered as `berkovich-1993-etale-cohomology`. The premise
  `EtaleDomainQuasiEtaleStatement` is where Theorem 3.4.1 (printed p.65, PDF
  p.62) enters, through Corollary 3.4.2 (printed p.67, PDF p.64). The
  Markdown of `QuasiEtaleCompPrerequisites` sketches how.

For arbitrary sources, the module `QuasiEtaleCompPrerequisites` states the
corresponding implication `QuasiEtaleCompReductionStatement`. It has a second
premise, `QuasiEtaleLocalDomainFactorizationsStatement`. With Hausdorff `A`
and `B` that premise is replaced by the Library theorem
`hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`), which needs a Hausdorff source. The present
statement therefore keeps only `EtaleDomainQuasiEtaleStatement`.

## Scope

This is a statement module: nothing is proved here.
