# The central split Isogeny Theorem with the actual torus map

Author: Worker 4302 (Task 4302, `4c17faf9-bffb-4e8c-98fd-a69a6d711236`).

The imported `Langlands.GroupScheme.splitCentralIsogenyExistence` proves exactly the published
proposition `Langlands.GroupScheme.SplitCentralIsogenyExistenceStatement.{u}`
(module [`SplitClassificationStatement`](SplitClassificationStatement.md)), at
every universe `u`, with no hypotheses.

## The statement

Let `k : Type u` be any field. No perfectness or characteristic hypothesis is
added, so imperfect fields and positive characteristic are included. Let `G`
and `G'` be connected reductive group schemes over `Spec k`
(`IsConnectedReductive`). Let `i : T ⟶ G` and `i' : T' ⟶ G'` be maximal tori
(`IsMaximalTorus`) whose tori are split (`IsSplitTorus`). Let `P` and `P'` be
root data of `i` and `i'` in the sense of `IsRootDatumOf`. Let
`f : RootPairing.Hom P' P` be a morphism of root pairings whose weight map
`X(T') → X(T)` and coweight map `Y(T) → Y(T')` are both injective. Then there
are actual morphisms `φ : G ⟶ G'` and `t : T ⟶ T'` such that:

- `i ≫ φ = CommGroupScheme.groupHom t ≫ i'`;
- `f.weightMap χ = t ≫ χ` for every character `χ : characterLattice T'`;
- `IsCentralIsogeny φ`, with the Library's scheme-theoretic kernel and centre.

The torus map `t` is part of the conclusion. The theorem does not take `t`, a
group isogeny, a cover, a lifting law or a torus/lattice anti-equivalence as a
premise.

## Implemented proof

The reviewed contribution is the single-term reuse of
`Langlands.GroupScheme.splitCentralIsogenyExistence` from
[`SplitCentralIsogenyExistenceProof`](SplitCentralIsogenyExistenceProof.md).
That theorem already has type `SplitCentralIsogenyExistenceStatement.{u}`.
The contribution's duplicate name `splitCentralIsogenyTheorem` was consolidated
into this existing declaration during integration. This module imports the proof
and adds no declaration; the reviewed proposition and its proof remain available
under `splitCentralIsogenyExistence`.

The original proof predates this project instance. Worker 4302 submitted its
reuse for Task 4302 as artifact `3eb372a0-2b5e-4ecb-9854-eb519c080485`, following
the operator's direction for carried-over results (answer to request
`19bb560bdd4a5797b0f6c0ef021e7963`, Task 3798). Independent acceptance concerns
this exact target; the contribution adds no mathematics.

The Markdown of `SplitCentralIsogenyExistenceProof` describes that proof. It
applies the reduction `splitCentralIsogenyExistence_of_commonTorusIsomorphism`
([`SplitCentralIsogenyReduction`](SplitCentralIsogenyReduction.md)) to four
unconditional Library proofs:

1. `rootDatumExistence` ([`RootDatumExistence`](RootDatumExistence.md)): every
   split maximal torus of a connected reductive group has a root datum.
2. `centralIsogenyRootDatumHom`
   ([`CentralIsogeny.SplitRootDatumProof`](../CentralIsogeny/SplitRootDatumProof.md)):
   a central isogeny `q` with `i ≫ q = t ≫ i''` defines a morphism of root
   pairings with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`.
3. `splitCentralTorusQuotient`
   ([`CentralTorusQuotientProof`](CentralTorusQuotientProof.md)): if
   `t : T ⟶ T'` maps to a split torus, is injective on characters and
   cocharacters, and every root of `i` has the form `t ≫ α'`, then there are a
   connected reductive group `Q`, a central isogeny `q : G ⟶ Q` and a maximal
   torus `i'' : T' ⟶ Q` with `i ≫ q = t ≫ i''`.
4. `splitCommonTorusIsomorphism`
   ([`SplitIsomorphismProof`](SplitIsomorphismProof.md)): two connected
   reductive groups with maximal tori `i₁`, `i₂` on the same split torus, whose
   root data match under a reindexing of roots and coroots, are isomorphic by
   some `ψ` with `i₁ ≫ ψ.hom = i₂`.

The reduction runs as follows.

- **The torus map.** It constructs `t : T ⟶ T'` with `t ≫ χ = f.weightMap χ`
  from `IsSplitTorus.exists_hom_of_characterMap`
  ([`Torus.CharacterMapHom`](../Torus/CharacterMapHom.md)). That theorem builds
  `t` explicitly from a splitting `e : T' ≅ 𝔾ₘ^I`: with `F = f.weightMap` and
  the coordinate characters `ψᵢ` of `T'`, it takes
  `t = (∑ᵢ F(ψᵢ) ≫ singleᵢ) ≫ e⁻¹`. No anti-equivalence is assumed. Since
  both root data use the Library's lattice pairing,
  `RootDatumHom.coweightMap_apply_of_weightMap`
  ([`RootDatumHomLattices`](RootDatumHomLattices.md)) gives
  `f.coweightMap ν = ν ≫ t`.
- **The central quotient.** The two lattice maps of `t` are injective because
  they are the weight and coweight maps of `f`. Every root `P.root j` equals
  `t ≫ P'.root (f.indexEquiv.symm j)`. Item 3 then gives `Q`, `q` and `i''`.
- **The root data on `T'`.** Item 1 gives a root datum `P''` of `i''`, and
  item 2 gives `f'' : P'' ⟶ P` with the same weight and coweight maps as `f`.
  Reindexing along `J'' ≃ J ≃ J'`, the roots of `P''` and `P'` agree because
  the weight map is injective. Their coroots agree because both coroot families
  are images of the coroots of `P` under the coweight map.
- **Conclusion.** Item 4 gives `ψ : Q ≅ G'` with `i'' ≫ ψ.hom = i'`. The
  reduction takes `φ = q ≫ ψ.hom`, a central isogeny by
  `IsCentralIsogeny.comp_iso`, and `t` as the torus map.

## Scope checks

- The theorem type is exactly `SplitCentralIsogenyExistenceStatement.{u}`.
  The independently reviewed alias had the same checked type fingerprint as
  the retained `splitCentralIsogenyExistence` declaration.
- No result about simply connected covers is used. The import closure of this
  module contains no module under `Langlands.GroupScheme.SimplyConnected`, and
  no module that mentions `SplitSimplyConnectedCoverExistenceStatement` or the
  general `SimplyConnectedCoverExistenceStatement`.

## Relation to the literature

The statement is Milne, *Algebraic Groups* (2017), Theorem 23.9, central case,
with Definitions 23.1–23.2 and Proposition 23.5; see the statement's Markdown.
Milne proves the sufficiency half in Section 23b (printed pp.487–492). Lemma
23.13 reduces to split semisimple groups, Proposition 23.14 treats semisimple
rank one, and Steinberg's graph argument (23.15–23.24) treats the general case,
finishing with big cells. The implemented route is different. It forms the
quotient of `G` by the image of the scheme-theoretic kernel of `t`, a finite
central subgroup, and identifies this quotient with `G'` by the
Isomorphism Theorem for a common split torus (the isomorphism case of Milne
Theorem 23.25, stated as Remark 23.26). The Library proves that theorem
separately, from its rank-one case and a Levi gluing argument
(`splitRankOneCommonTorusIsomorphism`, `splitCommonTorusLeviGluing`).

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
