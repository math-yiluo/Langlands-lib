# Statements: an ingredient of the composition of quasi-étale morphisms

Author: Worker 385.

This module states, without proof, a property of the Library predicate
`quasiEtale` on the localized category `LocalizedCategory.{u, v, v} (K := K)`.
It also states that this property, together with
`QuasiEtaleLocalDomainFactorizationsStatement`, implies the composition
clause `QuasiEtaleCompStatement` of Berkovich 1994, Lemma 3.1(i). The two
Prop-valued definitions are in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. Each takes a complete
ultrametric normed field `K : Type u` as an explicit argument. The universes
are those of `QuasiEtaleCompStatement`: `u` for the field and `v` for the
spaces and atlas indices.

## The statements

1. `EtaleDomainQuasiEtaleStatement K`: let `D` be an analytic domain of `W`
   and `e : E ⟶ domainObj W D` an étale morphism into the domain. Then
   `e ≫ domainι W D` is quasi-étale. Here `domainι W D` is the inclusion of
   the domain. The Library has the other order:
   `quasiEtale_domainι_comp_of_etale` says that a domain inclusion followed by
   an étale morphism is quasi-étale.
2. `QuasiEtaleCompReductionStatement K` is the implication
   `QuasiEtaleLocalDomainFactorizationsStatement K →
   EtaleDomainQuasiEtaleStatement K → QuasiEtaleCompStatement K`.
   - `QuasiEtaleLocalDomainFactorizationsStatement K` (module
     `QuasiEtaleLocalDomainFactorizationsStatement`, by Worker 974) says that
     every quasi-étale morphism `f` satisfies
     `HasLocalDomainEtaleFactorizations f`. That is, at every point `y` of
     the source there is a finite set of analytic domains of the source that
     all contain `y` and whose union is a neighbourhood of `y`. On each of
     them the restriction of `f` is an analytic-domain embedding followed by
     an étale morphism. No Hausdorff hypothesis is made. The Library proves
     the Hausdorff case (`hasLocalDomainEtaleFactorizations_of_quasiEtale`).
   - `QuasiEtaleCompStatement K` (module `QuasiEtaleStabilityStatement`) is
     the Mathlib class `MorphismProperty.IsStableUnderComposition quasiEtale`.

No Hausdorff, compactness or smallness hypothesis is imposed on any object.

## Original source and provenance

Both statements are derived. Statement 1 is not stated in the source.
Statement 2 is the composition clause of the source, with two ingredients
of its one-line proof made into named premises.

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed
pp.543–544 (PDF pp.5–6). The definition: a morphism `φ : Y → X` is
quasi-étale if for every point `y ∈ Y` there are affinoid domains
`V₁, …, Vₙ ⊂ Y` such that `V₁ ∪ … ∪ Vₙ` is a neighbourhood of `y` and each
`Vᵢ` can be identified with an affinoid domain in a k-analytic space étale
over `X`. Right after the definition, Berkovich notes that étale morphisms and
the embeddings of analytic domains are quasi-étale. Then comes Lemma 3.1:

> (i) Quasi-étale morphisms are preserved under compositions, under any base
> change functor and under any ground field extension functor.
>
> Proof. All the statements easily follow from the corresponding properties
> of étale morphisms and Theorem 3.4.1 from [Ber2].

[Ber2] is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
Publ. Math. IHÉS 78 (1993), registered as `berkovich-1993-etale-cohomology`.
Its Theorem 3.4.1 (printed p.65, PDF p.62) says the following. Let `X` be a
k-analytic space and `x ∈ X` a point. Then there is an equivalence of
categories `FÉt(X, x) ≃ FÉt(𝓗(x))`. Here `FÉt(X, x)` is the category of
finite étale germs over `(X, x)`. For a field `K`, `FÉt(K)` is the category
of schemes finite and étale over `Spec K`, as defined in the paragraph just
before the theorem. Finite étale `K`-algebras with their usual homomorphisms
form the opposite category, so with algebras the comparison is an
anti-equivalence. Corollary 3.4.2 (printed p.67, PDF p.64) is the
base-change form. Let `φ : Y → X` be a morphism, `y ∈ Y` and `x = φ(y)`.
Suppose the maximal purely inseparable extension of `𝓗(x)` in `𝓗(y)` is
dense in `𝓗(y)`. Then `U ↦ U ×_X Y` induces an equivalence
`FÉt(X, x) ≃ FÉt(Y, y)`.

How the statements relate to the source:

- Statement 1 is where Theorem 3.4.1 enters. Here is a sketch of the
  expected argument; the source does not spell it out. Let `D` be an
  analytic domain of `W` and `d ∈ D` a point. The completed residue field
  `𝓗(d)` is the same whether `d` is viewed in `D` or in `W`. So the
  hypothesis of Corollary 3.4.2 holds for the inclusion `D → W` at `d`, and
  restriction `U ↦ U ×_W D` is an equivalence `FÉt(W, d) ≃ FÉt(D, d)`. In
  particular, every finite étale germ over `(D, d)` is, up to isomorphism,
  the restriction of a finite étale germ over `(W, d)`. Near a point over
  `d`, an étale space over `D` is then an analytic domain of a space étale
  over `W`. Only this statement on objects (up to isomorphism) is used, so
  the variance of the comparison plays no role in the sketch.
- The premise `QuasiEtaleLocalDomainFactorizationsStatement` adds a
  condition to the source definition: every domain of the finite family
  contains the point `y`. The source definition does not ask for this. In a
  Hausdorff space the condition costs nothing. Affinoid domains are compact
  and so closed, so a domain missing `y` can be dropped. Without a Hausdorff
  hypothesis, a compact domain that misses `y` may still accumulate at `y`.
- The other ingredient of the source proof is étale base change along a
  domain inclusion. It is already a Library theorem:
  `localizedEtalePullbackBaseChange` (module `LocalizedEtalePullbackProof`).
  So it is used in the proof of statement 2, not assumed.

The following is an informal remark and is not formalized here: both
premises of statement 2 are logical consequences of
`QuasiEtaleCompStatement`. So the implication loses no generality: the two
premises are necessary for the conclusion and, by statement 2, sufficient.
This is a claim about logical strength only. It does not claim that every
proof of composition has to invoke the premises or go through them.

- For statement 1: `e` is étale, hence quasi-étale (`etale_le_quasiEtale`).
  Also `domainι W D` is quasi-étale (`quasiEtale_domainι`). Compose the two.
- For `QuasiEtaleLocalDomainFactorizationsStatement`: restrict `f` to an
  open Hausdorff neighbourhood of `y`. This restriction is the composite of
  a domain inclusion and `f`, so it is quasi-étale. Then apply the Library's
  Hausdorff case and transport the domains back to the source of `f`.

## Use

The companion module `QuasiEtaleCompReduction` proves statement 2 as
`quasiEtaleCompReduction`. Once both premises are proved, it gives
`QuasiEtaleCompStatement`, the target of Task 7909.

## Scope

This is a `lean.statement`: nothing is proved here.
