# Properties of a special maximal compact subgroup

Worker 1249, task `219b673d-b7f3-47fb-9019-d1642687d4ac`.

This module defines proposition-valued predicates on a subgroup `K` of the
actual rational points `G(F)`. They express the properties of a special
maximal compact subgroup in Kaletha–Prasad Theorem 4.2.15(1) and in Renard,
Théorème V.5.1(2), (3), (5). The module also defines the standard-Levi
restriction relation and inheritance clause for the compact stabilizer at an
apartment point. It asserts nothing. The existence target that uses these
predicates is
`Langlands.BruhatTits.SpecialCompact.SpecialMaximalCompactExistence`.

All declarations are in the namespace `Langlands.BruhatTits.SpecialCompact`.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 2.2.1, Remark 2.2.2 and Fact 2.2.3 (PDF page 101); Theorem
  4.2.15(1) and its proof (PDF pages 204–205); Lemma 6.7.1 and §6.7.2
  (PDF pages 264–265).
- The registered corrections `kaletha-prasad-2024-corrections`, version
  1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. The
  Henselian convention for §2.2 (PDF page 24) is part of the local-field
  setting used here.
- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
  edition, registered as
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  Théorème V.5.1, printed page 122, PDF page 128.

## Topology and boundedness

The topology on `G(F)` is the named
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`. It
is installed locally with `letI`; no topology instance on rational points is
declared. The affineness of `G.X.left` needed by this topology and by
boundedness comes from `[IsAffineHom G.X.hom]` through
`isAffine_of_isAffineHom`. Boundedness is the published
`IsAlgebraicallyBounded F G.X`, which is KP Definition 2.2.1 for actual
regular functions.

- `IsBoundedOpenMaximal F K` is the source form of KP Theorem 4.2.15(1):
  `K` is algebraically bounded, open, and
  `Maximal (fun L => IsAlgebraicallyBounded F G.X L) K`. Mathlib's
  `Maximal P K` means that `K` satisfies `P` and every subgroup `L` with `P L`
  and `K ≤ L` satisfies `L ≤ K`. The theorem states "maximal open and
  bounded"; its proof shows that every bounded subgroup containing
  `G(k)^1_x` equals it, which is maximality among bounded subgroups. This is
  the form stated here, and it implies the stated form.
- `IsCompactOpenMaximal F K` is the local-field form used by Renard
  V.5.1: `K` is compact, open, and maximal among compact subgroups.

The comparison between the two forms is KP Fact 2.2.3. Its local-field case is
the published statement
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldAffineBoundedCompactnessProperty`.
That comparison is neither assumed nor used here: the conjunction below
requires both forms separately. Neither predicate needs a local field to be
formed. Only `[ValuativeRel F]` and `[TopologicalSpace F]` are required.

## Weyl representatives and parabolic factorization

Let `i : S.toGrp ⟶ G` be the chosen torus and `ν : cocharacterLattice S` the
cocharacter whose positive system fixes the minimal parabolic.

- `HasWeylRepresentatives i K` says that every `w : relativeWeylGroup i`
  equals `QuotientGroup.mk n` for some `n : normalizerPoints i` with
  `(n : rationalPoints G) ∈ K`. Here
  `relativeWeylGroup i = N(F)/Z(F)` is the actual relative Weyl group. The
  predicate says that `N(F) ∩ K → W` is surjective, which is Renard V.5.1(2):
  every `s ∈ W_G` has a representative in `K_0`.
- `HasParabolicFactorization i ν K` says that for every
  `J ⊆ simpleRelativeRoots i ν`, the subsets of `G(F)` satisfy
  `↑(K ⊓ standardParabolicPoints i ν J) =`
  `↑(K ⊓ standardLeviPoints i ν J) * ↑(K ⊓ standardUnipotentPoints i ν J)`.
  The product is the pointwise product of sets in `G(F)`, so this is the
  literal identity `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)` of Renard V.5.1(3) for the
  actual standard parabolic `P_J = M_J U_J`. The standard parabolics of
  Renard correspond to the subsets `J` of the simple roots (Renard V.4.2).
- `SpecialCompactProperties F i ν K` is the conjunction
  `IsBoundedOpenMaximal F K ∧ IsCompactOpenMaximal F K ∧`
  `HasWeylRepresentatives i K ∧ HasParabolicFactorization i ν K`.

Renard's V.5.1(1) (Iwasawa) and (4) (Cartan) are sibling targets. They are
not part of `SpecialCompactProperties`.

## Inheritance by standard Levi subgroups

- `IsLeviRestriction j y yM`, for `j : M ⟶ G`, apartment data
  `D : KPApartmentData i ω` and `DM : KPApartmentData iM ω`, and points
  `y : D.Apartment` and `yM : DM.Apartment`, says
  `yM.val a m = y.val a (rationalPoints.map j m)` for every
  `a ∈ relativeRoots iM` and every `m : rationalPoints M`. In KP §6.7, a
  valuation `φ` of the root datum of `(G, S)` restricts to
  `φ_M = (φ_a)_{a ∈ Φ(M,S)}`. Lemma 6.7.1 shows that `φ_M` is a valuation of
  the root datum of `(M, S)`, that compatibility with `ω` is preserved, and
  that `A(M,S) = {φ_M}` is an equipollence class. The point `yM` is therefore
  the image of `y` under the projection `A(S,G) → A(M,S)` of (6.7.1). The
  published `RootFunctionFamily` is a family of functions on all of `M(F)`,
  indexed by all characters of `S`. By the normalization fields of
  `IsRootDatumValuation`, only the values on the roots of `(M, S)` carry
  information. The equation is therefore imposed exactly there, for all
  `m : M(F)`, with the root groups of `M` mapped into `G(F)` by `j`.
- `SpecialLeviRestriction F ν D x J DM xM` is the relation for one set
  `J` of simple relative roots. Its parameters are apartment data
  `D : KPApartmentData i (localFieldOrder F)` for `(G, S)`, a point
  `x : D.Apartment`, and `J`. Let `M_J = Standard.leviScheme i ν J` be the
  actual closed representative of the standard Levi, with inclusion
  `Standard.leviHom i ν J : M_J ⟶ G` and the same torus
  `Standard.leviTorusHom i ν J : S.toGrp ⟶ M_J` inside `M_J`. The remaining
  parameters are
  `DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)` and
  `xM : DM.Apartment`. The instances `IsAffineHom` on `M_J` and `Mono` on the
  torus are parameters of the relation; `SpecialLeviInheritance` supplies the
  published ones. The relation is the conjunction of:
  1. `DM.IsSpecialApartmentVertex xM`: `xM` is a special vertex of the
     apartment of `M_J`;
  2. `IsLeviRestriction (Standard.leviHom i ν J) x xM`: `xM` is the
     restriction of `x`, so the apartment of `M_J` and its point are the
     inherited ones of KP §6.7;
  3. `SpecialCompactProperties F (Standard.leviTorusHom i ν J) ν`
     `(DM.specialCompactSubgroup xM)`: the compact stabilizer
     `M_J(F)^1 ∩ M_J(F)_{xM}` has properties (2), (3) and maximal
     compactness for `M_J`. These use the same torus and the same `ν`, hence
     the minimal parabolic `P_∅ ∩ M_J` of `M_J` that `ν` determines;
  4. `DM.specialCompactSubgroup xM = D.specialCompactLeviSubgroup ν J x`:
     this subgroup of `M_J(F)` is the preimage of `K_x` under the inclusion.
     By the published `specialCompactLeviSubgroup_map`, its image in `G(F)`
     is exactly `K_x ∩ M_J(F)`.

  The relation is a separate definition so that a later existence target can
  add further conditions on the Levi data `DM`, for example a validity
  predicate for apartment data, without changing these definitions.
- `SpecialLeviInheritance F hi ν D x`, for a maximal split torus
  (`hi : IsMaximalSplitTorus i`), says: for every
  `J ⊆ simpleRelativeRoots i ν` there exist `DM` and `xM` with
  `SpecialLeviRestriction F ν D x J DM xM`. The affineness of `M_J` is
  `(Standard.isClosedSubgroup_leviHom i ν J).isAffineHom`, and the `Mono`
  instance on the torus comes from
  `Standard.isMaximalSplitTorus_leviTorusHom i ν J hi`.

  This is Renard V.5.1(5): `K_0 ∩ M` is a maximal compact subgroup of `M`
  with properties (1)–(4) for `P_∅ ∩ M`. Of these, properties (2) and (3)
  and maximal compactness are imposed. The special-point part is KP §6.7.2:
  the image of a special point under (6.7.1) is special, in particular a
  vertex. The torus factorization `Standard.leviTorusHom`, its maximal
  splitness `Standard.isMaximalSplitTorus_leviTorusHom`, and
  `KPApartmentData.specialCompactLeviSubgroup` are the accepted adapters of
  Worker 1229 in `Langlands.Geometry.Building.SpecialCompactLevi`. The
  predicate quantifies over every `J`, so the one `x`, and hence the one
  `K_x`, serves every standard parabolic.

## Provenance

The predicates transcribe the cited source properties for the actual
published objects. The following choices are internal. Both the bounded and
the compact form are kept, rather than one being derived through Fact 2.2.3.
Maximality is expressed by Mathlib's `Maximal`. The restriction of valuations
is expressed through the normalized `RootFunctionFamily` encoding. Levi
inheritance uses the published closed representative `Standard.leviScheme`
in place of an abstract Levi subgroup.
