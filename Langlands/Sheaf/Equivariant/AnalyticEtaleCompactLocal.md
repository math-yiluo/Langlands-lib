# Compactly supported sections from local lifted actions

This internal construction uses the existing twisted étale site,
local-action system, point germs and support constructions. Its proofs derive
from those constructions; it makes no new assertion from external literature.
All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

Let `K` be a complete ultrametric normed field, `L` a normed `K`-algebra field,
`X` an analytic space and `ρ : G →* Aut X` a group action. Fix
`h : ∀ x, EtaleSite.PointAxioms L x`. Coefficients are modules over a
commutative ring `R` in universe `max u (v + 1) uL`. Starting with the
second lemma, `G` is a topological group.

The main results retain three explicit geometric hypotheses:

- `hlift : EtalePointLifting L (X := X)` says that every `L`-valued point lifts
  through each étale object whose underlying image contains its projection.
- `hX` says that `pointProjection L X` is surjective.
- `hopen` says that every structural map of an object of `EtaleSite X` induces
  an open map on underlying spaces.

The first lemma only needs `hlift`, and the second needs none of these three
hypotheses. This module does not prove these geometric hypotheses.

## From restrictions to germs

`etaleGlobalGermMap_eq_of_twisted_restriction_eq` considers a sheaf `F` on the
twisted étale site, an arrow `f` to its base object and two global sections
whose restrictions along `f` agree. Their ordinary étale global germs agree at
every `L`-valued point projecting into the underlying image of `Hom.left f`.
The proof untwists `f` to an ordinary étale arrow. Restriction along the
invertible relabeling detects equality. The support-neighborhood criterion
applied to the difference of the two sections then makes its germ zero;
linearity gives equality of the original germs.

`exists_openSubgroup_twisted_restriction_eq` starts with a module presheaf,
a lifted action of an open subgroup on the source of `f` and a discrete
restriction of a global section. The local equivariance of `f` gives a smaller
open subgroup `M`. Every element of `M` sends the underlying image of `f` into
itself, and restricting its translate of the global section along `f` gives
the original restriction. To obtain the positive group action on the image,
the proof uses local equivariance at the inverse group element. Presheaf
functoriality and the subgroup fixing the discrete restriction give the
restriction equality.

`exists_open_invariant_etaleGlobalGermMap_eq` assumes `hlift`, `hX`, `hopen`
and local discreteness of the twisted étale sheaf `F`. For each underlying
point and each global section `s`, it supplies an open neighborhood `W` and
an open subgroup `M` preserving `W` such that `s` and each of its `M`-translates
have equal global germs over `W`. Surjectivity first supplies an `L`-valued
lift of the point. The point's covering axiom applied to the discrete sieve
produces a pointed arrow factoring through an arrow with discrete restriction.
The image of the latter arrow contains the chosen underlying point. After
translation its structural map is étale, so `hopen` makes this image open.
The two preceding lemmas give its subgroup invariance and germ equality.

## Compact support and smoothness

`isSmoothVector_of_isCompact_etaleUnderlyingSupport` assumes the same three
geometric hypotheses and local discreteness. It proves that a global section
with compact actual underlying support is a smooth vector of the published
`actionRepresentation`. Compact-set induction combines the preceding local
neighborhoods: finite unions of neighborhoods correspond to finite
intersections of open subgroups. The result is a set `W` containing the entire
support and an open subgroup preserving `W`, with germ equality there for all
its elements. The support-action fixed-section criterion then proves that
every element of this subgroup fixes the original section.

`isSmooth_etaleCompactRepresentation_of_locallyDiscrete` proves that the full
representation of compactly supported global sections of `F` is smooth.
The support-descent compactness criterion turns membership in the published
compact-support submodule into compactness of the actual underlying support.
The preceding theorem supplies a subgroup fixing the underlying global
section; subtype extensionality makes it fix the compactly supported section.
The topology on `L`-valued points is the published `pointTopology`.

## The canonical degree-zero comparison

`isIso_etaleCompactInclusion` proves that the canonical natural transformation
`etaleCompactInclusion L ρ h R` is an isomorphism. An étale `G`-sheaf has local
discreteness by definition. Thus every compactly supported section is smooth,
so the componentwise inclusion of the smooth part is both injective and
surjective. The componentwise criterion for a natural isomorphism completes
the proof.

`etaleCompactSectionsIso` packages this inclusion as the natural isomorphism

```text
etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G
  ≅ etaleGSheafRestriction ρ R ⋙ etaleCompactSections L h R.
```

Here `smoothForget` is the underlying-module functor on smooth
representations, defined in `Langlands.Sheaf.Equivariant.TwistedOver`.
`etaleCompactSectionsIso_hom` records that the forward natural transformation
is exactly the canonical `etaleCompactInclusion`.

All three geometric hypotheses remain explicit in this isomorphism.
No compactness hypothesis on the whole space, Hausdorff hypothesis,
smallness of `G`, admissible-refinement assumption or additional continuity
assumption on the action is used in this conditional degree-zero result.
The higher-degree compact-cohomology comparison remains a separate obligation.
