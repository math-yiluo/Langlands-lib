# Statement: the morphisms of sites `μ : X_qét → X_ét` and `μ_G : X(G)_qét → X(G)_ét`

Author: Worker 21.

This module states, without proof, that the inclusion of the étale category
into the quasi-étale category defines a morphism of sites, both for an
analytic space `X` and for a `G`-space `X(G)`. The statement is the
proposition
`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleToEtaleStatement`.

## Original sources

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed
p.544, after the definition of the quasi-étale site:

> It is clear that there is a morphism of sites μ : X_qét → X_ét.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.3, after the definition of `X(G)_qét` and `X(G)_ét`:

> There is a morphism of sites μ_G : X(G)_qét → X(G)_ét

Neither text gives a proof.

## Statement

`QuasiEtaleToEtaleStatement : Prop`. For every complete ultrametric normed
field `K : Type u`:

1. for every analytic space `X : LocalizedCategory.{u, v, v}`, the inclusion
   `EtaleSite.toQuasiEtaleSite X : Ét(X) ⥤ Qét(X)` (module `QuasiEtaleSite`)
   is representably flat (Mathlib's `RepresentablyFlat`) and continuous
   (Mathlib's `Functor.IsContinuous`) for the étale topology `etaleTopology X`
   and the quasi-étale topology `quasiEtaleTopology X`;
2. for every group `G : Type z` with a topology and every `G`-space
   `X : GSpace.{u, v, v} K G`, the inclusion
   `EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X : Ét(X(G)) ⥤ Qét(X(G))`
   (module `EquivariantQuasiEtaleSite`) is representably flat and continuous
   for `equivariantEtaleTopology X` and `equivariantQuasiEtaleTopology X`.

A morphism of sites goes in the opposite direction to the functor that
defines it: the inclusion `Ét → Qét` defines `μ : X_qét → X_ét`.

## How the statement renders "morphism of sites"

As in the Library's statement `SetInducedSpace.MorphismOfSitesStatement`
(module `SetInducedSiteStatement`): a morphism of sites in the sense of SGA 4
(IV 4.9.1) is given by a continuous functor whose pullback of sheaves is left
exact. Mathlib's module `Mathlib.CategoryTheory.Sites.Pullback` describes a
continuous, representably flat functor as such a morphism. For a
representably flat functor, Mathlib's
`Functor.isContinuous_iff_coverPreserving` shows that continuity is the same
as preserving covering sieves.

Representable flatness says that for every quasi-étale `U` over `X` the
category of pairs `(V, U → V)` with `V` étale over `X` and `U → V` over `X` is
cofiltered. The statement does not mention fibre products, which the Library
does not have in general.

## Notes

- Berkovich's sites are on a `G`-space for a topological group `G`. The
  Library's categories `Ét(X(G))` and `Qét(X(G))` only need a group with a
  topology, and the statement is quantified the same way.
- The expected proof: étale morphisms are open, so an étale covering is a
  quasi-étale covering; flatness uses fibre products `V₁ ×_X V₂` of spaces
  étale over `X` and the openness of the equalizer of two morphisms between
  spaces étale over `X`.
- This is a `lean.statement`: nothing is proved here.
