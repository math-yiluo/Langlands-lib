# Existence of a compact open Iwasawa subgroup of `G(F)`

Author: Worker 826 (Task 7286). The minimal interface was agreed with Worker 334,
the first executor of Task 7286. Their staged adapter will use it.

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalIwasawaCompactExistence`,
namespace `Langlands.HarishChandraSchwartz`, universe `u`.

## The statement

`RationalIwasawaCompactExistenceStatement.{u}` is the following proposition. Fix:

- a nonarchimedean local field `F : Type u`, with the standard instance binders
  `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`;
- a group scheme `G` over `Spec F` with `[IsAffine G.X.left]` and
  `[LocallyOfFiniteType G.X.hom]`;
- a proof that `G` is connected reductive (`IsConnectedReductive G`).

Give `G(F) = rationalPoints G` its canonical topology `rationalPointTopology F G.X`.
Then there exist:

- a commutative group scheme `S` and a morphism `i : S.toGrp ⟶ G` with
  `IsMaximalSplitTorus i`;
- a cocharacter `ν : cocharacterLattice S` with `IsGenericCocharacter i ν`;
- an open subgroup `K : OpenSubgroup (rationalPoints G)` that is compact.

These satisfy `IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup`. That is, every
`g ∈ G(F)` can be written as `g = p * k` with `p` in the rational points `P₀(F)` of the
empty-index standard parabolic subgroup of `(i, ν)`, and `k ∈ K`.

The binders are the same as in the published targets of Task 7286, such as
`RationalFixedCoefficientFinitenessStatement`. So the statement can be used directly
inside their proofs.

### Mathematical meaning and provenance

This is the Iwasawa decomposition `G = P₀ K` for a minimal parabolic subgroup `P₀`
and a compact open subgroup `K`. Only its existence is asserted, with the torus, the chamber
and `K` all existentially quantified. The literature states it for a special maximal compact
subgroup:

- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
  Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), §I.1, printed p.240 / PDF p.6 (registered
  source `waldspurger-2003-plancherel`). The paper fixes a maximal compact subgroup `K` that
  is the fixer of a special point of the apartment of `A₀`. It then states: "Soit P = MU un
  sous-groupe parabolique semi-standard de G. Alors G = PK". The case `P = P₀` is the
  present statement.
- T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 5.3.4,
  printed pp.190–191 / PDF pp.221–222 (registered source
  `kaletha-prasad-2023-bruhat-tits-new-approach`). It gives both parahoric product orders
  for a special vertex and every parabolic subgroup.

Provenance is **derived**. The statement weakens the cited theorems. It keeps the factorization
`G(F) = P₀(F) K` and the compactness and openness of `K`. It forgets that `K` is a special
maximal compact subgroup, and it forgets that the torus and chamber can be prescribed. The
analytic interfaces of Waldspurger VIII in the Library only need these structural choices.
One example is `RationalCuspidalCentralProjectionFiniteStatement.fixedCoefficientFiniteness`,
which takes `i`, `ν`, a compact open `K` and `IsIwasawaPair (standardParabolicPoints i ν ∅) K`
as explicit data.

## Conditional proofs

Neither premise below is proved in the Library, so both theorems are conditional. This module
does not prove the statement outright.

### `rationalIwasawaCompactExistence_of_bruhatTitsAvailability`

Type: `BruhatTitsAvailabilityStatement.{u} → RationalIwasawaCompactExistenceStatement.{u}`.

1. Destructure the premise into a corrected Kaletha–Prasad assignment `𝔅` with `𝔅.IsValid`.
   Then `h𝔅.isAvailableFor` gives `𝔅.IsAvailableFor F G hG`.
2. Let `B = (𝔅.datum F G hG).base`. Its torus `B.i` is a maximal split torus
   (`B.isMaximalSplitTorus`). A generic cocharacter `ν` of it comes from
   `IsSplitTorus.exists_genericCocharacter`, applied to the split-torus clause of
   `B.isMaximalSplitTorus.isSplitSubtorus`.
3. `availableSpecialVertexExistence F G hG 𝔅 hA` gives a special apartment vertex `x`.
4. The first clause of `BruhatTits.Iwasawa.availableIwasawa F G hG 𝔅 hA ν hν` at `x` gives the
   literal product family `ParabolicPointProductFamily B.i ν (B.apartment.specialCompactSubgroup x)`.
   It also gives `IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x)`, whose first two
   components are compactness and openness. These define `K` as an `OpenSubgroup`.
5. The standard-parabolic component of the product family, at the empty index set
   (`hP.2.2.1 ∅ (Set.empty_subset _)`), gives the product equalities for `P₀(F)` and `K`.
   `isIwasawaPair_of_pointProductEqualities` turns them into `IsIwasawaPair`.

No torus rebasing is needed. The torus is that of the assigned datum, and the statement
quantifies over it existentially.

### `rationalIwasawaCompactExistence_of_iwasawaExistence`

Type: `BruhatTits.Iwasawa.IwasawaExistenceStatement.{u} →
RationalIwasawaCompactExistenceStatement.{u}`.

1. `RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG` chooses a maximal
   split torus `i : S.toGrp ⟶ G` with a generic cocharacter `ν`.
2. The premise at `(F, G, hG, S, i, hi, ν, hν)` gives apartment data `D` and a special vertex
   `x`. It also gives `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)` and
   `ParabolicPointProductFamily i ν (D.specialCompactSubgroup x)`.
3. From `SpecialCompactProperties`, take compactness (`hprops.2.1.1`) and openness
   (`hprops.2.1.2.1`) of `K = D.specialCompactSubgroup x`. As in the first proof, the
   empty-index standard-parabolic product equality gives `IsIwasawaPair` through
   `isIwasawaPair_of_pointProductEqualities`.

Worker 334 used the same extraction in the adapter they staged for Task 7286.

## Dependencies

- `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`. It reduces, by published
  reductions, to `GroupAxiomsExistenceStatement` and four focused Kaletha–Prasad statements.
  Those statements have their own tasks.
- `Langlands.BruhatTits.Iwasawa.IwasawaExistenceStatement` (premise only).
- `Langlands.BruhatTits.Iwasawa.availableIwasawa` (KP Theorem 5.3.4 on available data).
- `Langlands.BruhatTits.SpecialCompact.availableSpecialVertexExistence`.
- `Langlands.GroupScheme.IsSplitTorus.exists_genericCocharacter`.
- `Langlands.Aubert.General.RationalPointFamily.exists_maximalSplitTorus_genericCocharacter`.
- `Langlands.HarishChandraSchwartz.isIwasawaPair_of_pointProductEqualities`.
