# The Kaletha–Prasad axioms on a single apartment class

Module `Langlands.Geometry.Building.KPApartmentAxioms`, namespace
`Langlands.Geometry.Building`.

The published `KPApartmentData i ω` (module `KPApartment`) is an `N(k)`-stable equipollence
class `A` of valuations of the root datum of `(G, S)`. Its valuations satisfy KP axioms V 0–V 5
and the `S(k)`-part of V 6. The module `KPCentralizerCompatibility` adds the full axiom V 6 on
the actual centralizer `Z(k)`, as `D.IsOmegaCompatible C` for `C : CentralizerDatum i`.

This module adds axiom V 7 and the conditions of KP Axiom 4.1.6 that can be stated on the single
class `A`. They are collected in one predicate, `D.SatisfiesApartmentAxioms C`, so that a
statement can quantify over one `D` that satisfies all of them.

The predicate covers only part of the corrected KP Definition 4.1.26. Its name says that it is a
list of apartment axioms, not the full validity condition "Bruhat–Tits theory is available for
`G`". The section "Not included" lists the missing clauses. The predicate asserts no existence.
That such `D` and `C` exist for every connected reductive `G` is KP's construction (Definition
6.1.27 and Lemma 6.1.28 for quasi-split `G`, Chapter 9 in general), and it is not stated here.

## Setting

- `F` is a field with `[ValuativeRel F] [TopologicalSpace F]`. The predicate itself and the
  translation lemmas below also assume `[IsNonarchimedeanLocalField F]`.
- `i : S.toGrp ⟶ G` with `[Mono i.hom.hom.left]` and `[IsAffineHom G.X.hom]`, as in
  `KPApartment`. It is meant to be a maximal split torus of a connected reductive `G`.
- `D : KPApartmentData i (localFieldOrder F)`. Here `localFieldOrder F` is the published
  normalized valuation `ord : Fˣ → ℤ ⊆ ℝ` (module `KPBuilding`). This is the type of `D` for
  which `KPBuilding` defines the compact stabilizers `D.compactStabilizer` and
  `KPCentralizerCompatibility` defines `D.IsOmegaCompatible`.
- `C : CentralizerDatum i` is the published bundled actual centralizer `Z = Z_G(S)`
  (module `KPCentralizerCompatibility`). It contains `j : Z ⟶ G`, `s : S.toGrp ⟶ Z`, and the
  bijectivity that defines `ν = C.translation : Z(F) →* Multiplicative (V S)`, `ν = -ω_Z`.
  It also contains `C.toNormalizer : Z(F) →* N(F)`.

## Axiom V 7

KP axiom V 7 (Definition 6.1.2, book PDF p. 230, printed p. 199) reads: for `a ∈ Φ`, the
subgroups `U_{a,φ,r}`, `r ∈ ℝ`, are bounded open subgroups of `U_a(k)`, and they form a
neighbourhood base of `1` in `U_a(k)`.

`IsTopologyCompatible i φ` states this for a family `φ : RootFunctionFamily S G`. The topology on
`G(F)` is the published `rationalPointTopology F G.X`, KP's analytic topology of Remark 2.2.2,
put in place locally by `letI`. `U_a(F)` is `rootGroupPoints i a` with the subspace topology,
and `U_{a,φ,r}` is the published `rootFiltration i φ a r`. For every relative root `a`:

- `(nhds (1 : U_a(F))).HasBasis (fun _ => True) (fun r => U_{a,φ,r})`: the sets
  `U_{a,φ,r}`, pulled back to `U_a(F)`, form a basis of the neighbourhood filter of `1` in
  `U_a(F)`;
- each `U_{a,φ,r}` is open in `U_a(F)`;
- each `U_{a,φ,r}` satisfies `IsAlgebraicallyBounded F G.X`, the published boundedness of KP
  Definition 2.2.1 (module `PointTopology.AffineBoundedness`): every regular function on `G` has
  values of bounded-below valuation on the set.

For the valuations of `D`, that `U_{a,φ,r}` is a subgroup of `U_a(F)` is already part of the
published data (the V 1 fields `one_mem`, `mul_mem` and `inv_mem` of `IsRootDatumValuation`), so
it is not repeated. The top-level `IsTopologyCompatible i φ` does not assume that `φ` is a
valuation.

Derived formulation of "bounded". KP mean bounded as a subset of `U_a(k)`, with `U_a` a closed
subgroup scheme of `G`. The Lean condition is boundedness as a subset of `G(F)`, since the Library
has `U_a(F)` only as a set of points of `G` and no scheme `U_a`. The two agree. A bounded subset of
`U_a(k)` stays bounded in `G(k)` by KP Fact 2.2.4 applied to the inclusion. Conversely, for a
closed embedding `U_a → G` the restriction `k[G] → k[U_a]` is surjective, so boundedness can be
tested on restrictions of regular functions of `G` (Remark 2.2.2). This comparison is not
formalized, because there is no scheme `U_a` in the Library.

The Lean condition uses boundedness, not compactness. Over a nonarchimedean local field a closed
subset is bounded if and only if it is compact (KP Fact 2.2.3, book PDF p. 101, printed p. 70,
with the Henselian hypothesis of the corrections, which a local field satisfies).
The Library has this only as the unproved statement target
`LocalFieldAffineBoundedCompactnessProperty`, and the closedness of `U_a(F)` in `G(F)` is not in
the Library. So no compactness of `U_{a,φ,r}` is derived here.

Proved facts:

- `IsTopologyCompatible.vadd`: if `φ` satisfies V 7, so does every translate `v +ᵥ φ`,
  `v ∈ V(S)`. The translate has `U_{a,v+φ,r} = U_{a,φ,r-a(v)}` (published `rootFiltration_vadd`
  and `rootFiltration_vadd'`), so it has the same family of sets with a shifted index.
- `D.IsTopologyCompatible` says that every valuation in the class `A` satisfies V 7.
- `isTopologyCompatible_iff_of_mem hφ`: for `φ ∈ A`, `D.IsTopologyCompatible` holds if and only if
  `φ` satisfies V 7. The other elements of `A` are translates of `φ` (published
  `equipollent_of_mem`).

`D.IsTopologyCompatible` is defined for any `ω`, not only for `localFieldOrder F`.

## `Z(F)` on the apartment

- `IsOmegaCompatible.normalizerAffineEquiv_eq hD z`: under V 6, the affine automorphism
  `D.normalizerAffineEquiv (C.toNormalizer z)` of the apartment is
  `AffineEquiv.constVAdd ℝ D.Apartment [ν(z)]`, the translation by the class of `ν(z)` in
  `TranslationSpace i`. This is the published pointwise formula `IsOmegaCompatible.smul_eq_vadd`
  (Axiom 4.1.4 (A 1), book PDF p. 190) stated as an equality of affine equivalences.
- `SatisfiesApartmentAxioms.constVAdd_mem_extendedAffineWeylGroup hD z`: these translations lie
  in `W(Ψ)ᵉˣᵗ`. Proof: rewrite with the previous lemma and use the AS 5 field
  `range_le_extendedAffineWeylGroup`.

## The predicate

`D.SatisfiesApartmentAxioms C : Prop` is a structure with the following fields.

- `omegaCompatible : D.IsOmegaCompatible C`. This is V 6 on `Z(F)`.
- `topologyCompatible : D.IsTopologyCompatible`. This is V 7.
- AS 2 (Axiom 4.1.6, book PDF p. 190): `isAffineRootSystem_extendedAffineRoots`, that is,
  `IsAffineRootSystemWithRankZero D.extendedAffineRoots` from the `RankZeroAffineRootSystem` module (KP
  Definition 1.3.1 with the corrected AR 4). Its AR 1 spanning clause is the derivative form
  "`∇Ψ` spans `V*`". This form admits KP's rank-zero system `∅` on a point, and for nonempty
  `Ψ` it is equivalent to KP's printed "`Ψ` spans `A*`" (`IsAffineRootSystemWithRankZero.span_eq_top` in
  `RankZeroAffineRootSystem`). With the printed clause, AS 2 could never hold for a group without
  relative roots; see the section "Rank zero". `derivativeRoots_extendedAffineRoots` says that its
  set of derivatives is `Φ`, as the image `Set.range (rootForm i)` of the relative roots in the
  dual of `TranslationSpace i`.
- AS 3: `isAffineRootSystem_affineRoots` and `derivativeRoots_affineRoots`, the same two
  statements for `Ψ = D.affineRoots`.
- AS 4: `mem_or_two_smul_mem`. For `ψ ∈ Ψ′`, at least one of `ψ` and `2ψ` lies in `Ψ`.
- AS 5, first sentence: `affineWeylGroup_le_range` and `range_le_extendedAffineWeylGroup`.
  The image of `D.normalizerAffineEquiv : N(F) →* (A ≃ᵃ[ℝ] A)` contains the affine Weyl group
  `W(Ψ)` (published `affineWeylGroup`) and is contained in `W(Ψ)ᵉˣᵗ` (published
  `extendedAffineWeylGroup`, KP 1.3.71).
- AS 5, second sentence: `range_eq_affineWeylGroup_of_isSimplyConnected`. If `G` is simply
  connected (published `IsSimplyConnected G`, module `GroupScheme.SimplyConnected.Basic`; it
  includes semisimplicity, as in KP's usage), the image is `W(Ψ)`.
- AS 5, third sentence: `range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint`. If `G`
  is quasi-split and adjoint (published `IsQuasiSplit G` and `IsAdjoint G`, modules
  `GroupScheme.Reductive.QuasiSplit` and `GroupScheme.Reductive.Semisimple`), the image is
  `W(Ψ)ᵉˣᵗ`.

Provenance of the AS fields:

- The sets are the published `D.extendedAffineRoots` and `D.affineRoots`. They are defined by
  the jumps of the filtrations `U_ψ` (KP Definition 6.3.4). Axiom 4.1.6 defines `Ψ′` from the
  hyperplanes `H_u` fixed by `m(u)`. KP Remark 4.1.7 recovers `Ψ′` as the set of jumps, which is
  the form used here. The corrections (PDF p. 27) add `∪ {1}` to `U_ψ` and `U_{ψ+}` in AS 3. The
  published affine root groups are subgroups, so they contain `1`.
- For the class `A(S)` these are KP's results. Proposition 6.3.13 (book PDF p. 252, printed
  p. 221) says that `Ψ` and `Ψ′` are affine root systems whose derivative root system is `Φ`, and
  that the image of `N(k)` in `Aff(A)` contains `W(Ψ)` and is contained in `W(Ψ)ᵉˣᵗ`.
  Proposition 6.3.8(2) says that if `ψ ∈ Ψ′ ∖ Ψ` then `2ψ ∈ Ψ`. Both are proved under V 7. In the
  corrected Definition 4.1.26 (corrections PDF p. 27) they are among the axioms that "Bruhat–Tits
  theory is available for `G`" requires. So the predicate takes these conclusions as conditions.
- The last two sentences of AS 5 are known for quasi-split `G` by Propositions 6.3.13 and 6.6.2.
  For general `G` the corrections (PDF p. 33) note that AS 5 amounts to the simply connected
  sentence, proved in Proposition 9.4.35 when the residue field is perfect. Chapter 7 of KP
  assumes AS 5. Here all three sentences are conditions.

## Rank zero

`satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty h`: if `relativeRoots i = ∅`, then
`D.SatisfiesApartmentAxioms C ↔ D.IsOmegaCompatible C`. So for a group without relative roots,
for instance a torus, the predicate is exactly V 6. It is not vacuously false.

Proof. With no relative roots, `rootAnnihilator i` is all of `V(S)`, because its defining
condition quantifies over the empty set of roots (published `mem_rootAnnihilator`). So
`TranslationSpace i` is zero (Mathlib's `Submodule.Quotient.subsingleton_iff`), and the
apartment, a torsor under it, is a single point. Then:

- `Ψ′ = Ψ = ∅` and `Set.range (rootForm i) = ∅`, since each of these sets is indexed by
  relative roots. So AS 2 and AS 3 hold by `isAffineRootSystemWithRankZero_empty_iff`, which is KP's
  rank-zero system (KP, after Definition 1.3.1, book PDF p. 46: the rank `dim V` "is positive
  precisely when `Ψ ≠ ∅`"). The derivative sets are `∇∅ = ∅ = Φ`.
- AS 4 and V 7 quantify over `Ψ′ = ∅` and over the relative roots, so they hold vacuously.
- The group of affine automorphisms of a point is trivial. So every subgroup inclusion and
  equality in the three AS 5 sentences holds.

## Axiom 4.1.2 on the reduced building

KP Axiom 4.1.2 (book PDF p. 189, printed p. 158): "The stabilizer `G(k)^1_x` of a point
`x ∈ B(G)` for the action of `G(k)^1` is a bounded open subgroup of `G(k)`."

`D.HasBoundedOpenStabilizers` states this for the published reduced building
`D.ReducedBuilding` (KP (7.6.2), Remark 7.6.5) and its published `G(F)`-action. For every point
`y`, the subgroup `D.compactStabilizer y = G(F)^1 ⊓ G(F)_y` must be open in `G(F)` for
`rationalPointTopology F G.X`, and its underlying set must be `IsAlgebraicallyBounded F G.X`
(KP Definition 2.2.1). Here `G(F)^1` is `Plancherel.rationalCommonNormKernel G` (KP Notation
2.6.15). As for V 7, boundedness is KP's algebraic notion. Its comparison with relative
compactness (Fact 2.2.3) is not used.

This predicate is separate from `SatisfiesApartmentAxioms`, because it concerns the building and
not the class `A(S)`. For the reduced building built from `D`, KP derive this axiom from the
valuation axioms (Chapter 7). That derivation is not formalized, so the predicate is a
condition.

## Not included

- AS 1 (the reflection `m(u)` fixes the hyperplane `H_u`) and the original form of AS 2 with
  `ψ^u_a`. They need the elements `m(u) = u′ u u″` of KP Proposition 2.11.17, which are not in
  the Library.
- AS 6, and Axioms 4.1.1, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22 of the corrected
  Definition 4.1.26 (Axiom 4.1.2 is the separate predicate above). They concern the building's
  polysimplicial structure, all apartments `A(S′)` with the maps
  `A(S) → A(gSg⁻¹)`, `G(k)^0`, integral models and the functoriality of `G ↦ B(G)`. They are not
  conditions on one `D`.
- The existence of `C` and of a `D` satisfying the predicate for a given `G`.
- Compactness of the `U_{a,φ,r}` (see the section on V 7).

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  - Definition 2.2.1, Remark 2.2.2, Facts 2.2.3 and 2.2.4 (book PDF p. 101, printed p. 70);
  - Notation 2.6.15 and Lemma 2.6.16 (book PDF pp. 133–134, printed pp. 102–103);
  - Definition 1.3.1 and the rank sentence after it (book PDF pp. 45–46, printed pp. 14–15);
  - Axiom 4.1.2 (book PDF p. 189, printed p. 158);
  - Axiom 4.1.4(A 1) (book PDF p. 190, printed p. 159);
  - Axiom 4.1.6, AS 1–AS 6, and Remark 4.1.7 (book PDF pp. 190–191, printed pp. 159–160);
  - Definition 6.1.2, V 6 and V 7 (book PDF p. 230, printed p. 199);
  - Definition 6.3.4, Proposition 6.3.8 and Proposition 6.3.13 (book PDF pp. 249–252, printed
    pp. 218–221).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  - PDF p. 24, §2.2: `k` is assumed Henselian in §2.2. A nonarchimedean local field is
    Henselian, so Fact 2.2.3 applies to `F`. The corrections do not change Definition 2.2.1,
    Remark 2.2.2, Fact 2.2.4 or V 7;
  - PDF p. 27, AS 3 with `∪ {1}` and the corrected Definition 4.1.26;
  - PDF p. 33, the assumption of AS 5 in Chapter 7.
