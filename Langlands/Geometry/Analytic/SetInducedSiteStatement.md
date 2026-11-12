# Statement: `γ : Σ ↦ X_Σ(G)` defines morphisms of sites

Author: Worker 21.

This module states, without proof, Berkovich's claim that the functor
`γ : Σ ↦ X_Σ(G)` defines morphisms of sites `X(G)_qét → P(G)` and
`X(G)_ét → P(G)`. The statement is the proposition
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace.MorphismOfSitesStatement`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.4:

> The correspondence Σ ↦ X_Σ(G) defines a morphism of sites
> γ : X(G)_qét → P(G) (resp. X(G)_ét → P(G)), and we see that Γ_{X{G}}(F) is
> exactly the G-set that represents the sheaf γ_*F.

Berkovich gives no proof.

## Statement

For every complete ultrametric normed field `K`, topological group
`G : Type z`, and `G`-space `X : GSpace.{u, max z v, max z v} K G`, and given
proofs `hC : ContinuityStatement` and `hD : SigmaDescStatement`:

1. the functor `quasiEtaleSiteFunctor hC X hD : P(G) ⥤ Qét(X(G))` is
   representably flat (Mathlib's `RepresentablyFlat`), and it is continuous
   (Mathlib's `Functor.IsContinuous`) for the topology
   `DiscreteGSet.topology G` of `P(G)` and the quasi-étale topology
   `equivariantQuasiEtaleTopology X`;
2. the functor `etaleSiteFunctor hC X hD : P(G) ⥤ Ét(X(G))` is representably
   flat and continuous for `DiscreteGSet.topology G` and the étale topology
   `equivariantEtaleTopology X`.

The functors are defined in module `SetInducedSite`. `P(G)` and its topology
are in module `DiscreteGSetSite`.

## How the statement renders "morphism of sites"

In SGA 4 (IV 4.9.1), a morphism of sites `(D, K) → (C, J)` is given by a
continuous functor `u : C ⥤ D` whose induced pullback of sheaves is left
exact. Mathlib's module `Mathlib.CategoryTheory.Sites.Pullback` describes a
continuous, representably flat functor as a morphism of sites in this sense.
For a continuous functor, the pullback of sheaves `Functor.sheafPullback` is
the left adjoint of `Functor.sheafPushforwardContinuous` when that adjoint
exists. Mathlib proves that it preserves finite limits for representably flat
functors under further hypotheses, for example for small sites. The statement
uses the two conditions, continuity and representable flatness. For a
representably flat functor, Mathlib's `Functor.isContinuous_iff_coverPreserving`
shows that continuity is the same as preserving covering sieves.

Representable flatness says that for every quasi-étale (resp. étale) `U(G)`
over `X(G)` the category of pairs `(Σ, U(G) → X_Σ(G))` is cofiltered. This
uses only the morphisms of `Qét(X(G))`, so the statement does not need fibre
products of analytic spaces, which the Library does not have in general.

## The hypotheses

`hC` and `hD` are statements that the Library has not yet proved. They are
taken as hypotheses only because the functors need them to be defined: `hC`
makes `X_Σ` a `G`-space, and `hD` makes the projection `X_Σ → X` quasi-étale
and étale. Since they are Props, the functors do not depend on the proofs. If
`hC` or `hD` were false, this statement would hold vacuously. A proof of this
statement may use `hC` and `hD`.
