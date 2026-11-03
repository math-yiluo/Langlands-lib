# The subgroups `T(K)^0`, `G(k)^♮` and `G(k)^0` of Kaletha–Prasad

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects (objective item 3). It
defines the Iwahori subgroup `T(K)^0` of a torus, the image `G(k)^♮` of the
simply connected cover, and the subgroup `G(F)^0` of KP Definition 2.6.23.
These are defined on the actual rational-point groups of actual group schemes.
The module `KPParahoric` uses `Z(F)^0` and `G(F)^0` from here to define the
parahoric subgroups.

The definitions need choices: a splitting field `L`, a maximally split
maximal torus `T`, a simply connected cover and a maximal split torus `S`.
These choices are data in two structures, `UnramifiedZeroDatum` and
`ZeroSubgroupDatum`. Nothing asserts that the data exist, and nothing proves
that the resulting subgroups are independent of the choices.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page numbers are the
PDF page numbers minus 31.

- §2.5(c), opening sentence, and Proposition 2.5.8, printed pp. 88–89, PDF
  pp. 119–120. `k` is a discretely valued Henselian field with perfect residue
  field, and `K` is the maximal unramified extension of `k` in a fixed
  separable closure `k^s`. For a `k`-torus `T`, the maximal bounded subgroup is
  `T(k)^b = ker(ω_T) = {x | ω(χ(x)) = 0 for all χ ∈ X^*(T)^Θ}
  = {x | ω(χ(x)) = 0 for all χ ∈ X^*(T)}`, where `Θ = Gal(k^s/k)`.
- Lemma 2.5.6, printed p. 88, PDF p. 119: a Galois extension `ℓ/k` of finite
  ramification degree is equipped with the unique valuation extending `ω`.
- Remark 2.5.11 and Lemma 2.5.12, printed p. 89, PDF p. 120: for a finite
  Galois extension `L/K` splitting `T`, the image of `T(L)^b` under the norm
  `T(L) → T(K)` is open and independent of `L`.
- Definition 2.5.13, printed p. 90, PDF p. 121: `T(K)^0` is the image of
  `T(L)^b` under the norm map `T(L) → T(K)`, for any finite Galois extension
  `L/K` splitting `T`; `T(k)^0 = T(K)^0 ∩ T(k)`.
- Definition 2.6.2, printed p. 93, PDF p. 124: a maximal `F`-torus `T ⊂ G` is
  maximally split if its maximal `F`-split subtorus is a maximal `F`-split
  torus of `G`.
- Corollary 2.3.8, printed p. 81, PDF p. 112: over `K` every connected
  reductive group is quasi-split.
- Definition 2.6.20, Facts 2.6.21 and 2.6.22, Definition 2.6.23 and
  Lemma 2.6.24, printed p. 104, PDF p. 135. Definition 2.6.20: `G(k)^♮` is
  the image of `G_sc(k) → G(k)`. Definition 2.6.23:
  1. if `G` is quasi-split, choose a maximally split maximal torus `T` and put
     `G(k)^0 = G(k)^♮ · T(k)^0`;
  2. if `G/Z(G)` is anisotropic, put `G(k)^0 = G(K)^0 ∩ G(k)`, with `G(K)^0`
     given by (1), since `G_K` is quasi-split;
  3. in general, choose a minimal Levi subgroup `M_0` and put
     `G(k)^0 = G(k)^♮ · M_0(k)^0`.
- Remarks 2.6.25 and 2.6.26, printed p. 105, PDF p. 136: the three parts of
  Definition 2.6.23 agree where they overlap; `G(k)^0 = G(K)^0 ∩ G(k)` is
  Proposition 9.3.24.
- Lemma 2.6.29, printed p. 106, PDF p. 137: `G(k)^0` has finite index in
  `G(k)^1`.

The corrections of 1 November 2024 (`kaletha-prasad-2024-corrections`) were
checked. PDF p. 24 removes the minus sign of `ω_T` in §2.5(b), changes the
cross-reference "§7" to "§6" in Remark 2.5.11 (the statement summarized above
is not affected) and replaces Remark 2.5.15. PDF p. 25 removes the minus sign of `ω_G` in §2.6(d), adds
before Definition 2.6.20 that `k` is Henselian with perfect residue field,
and in Definition 2.6.23 replaces "reductive group" by "reductive `k`-group".
The definitions here only use kernels: `ω(χ(x)) = 0` is the same condition
for either sign, and it is the condition `v(χ(x)) = 1` for the multiplicative
valuation `v`. Definitions 2.5.13, 2.6.2, 2.6.20 and the three parts of 2.6.23
are otherwise unchanged.

## Inputs

- Over an arbitrary field `k`: a group scheme
  `G : GroupScheme (Spec (CommRingCat.of k))`, its rational points
  `rationalPoints G` (that is, `G(k)`), its rational characters
  `rationalCharacters G` (the characters `X^*_k(G)` defined over `k`) with
  the evaluation `rationalCharacterEval χ : G(k) →* kˣ`, and a valuation
  `v : Valuation k Γ₀`.
- The torus predicates are the published ones: `IsMaximalTorus i` (module
  `GroupScheme.Torus.Maximal`), `IsMaximalSplitTorus i` (module
  `GroupScheme.Rational.SplitTorus`) and `IsSplitTorus` (a group scheme
  isomorphic to a split torus `𝔾_m^I`).
- The simply connected cover is the published `IsSimplyConnectedDerivedCover d π`
  for `d : D → G` and `π : C → D`. It says that `G` is connected reductive,
  `d` represents the derived subgroup of `G`, and `π` is a simply connected
  cover. So `C` is KP's `G_sc`.
- The local field: `F` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`. The topology enters only through these
  instances. A nonarchimedean local field is complete and discretely valued
  with finite, hence perfect, residue field, so KP's standing hypotheses of
  §2.5(c) and §2.6(e) hold for `F` and for `K`.
- KP's `K` is `UnramifiedClosure F`, the published
  `LocalGalois.Separable.inertiaFixedField F`, the fixed field of the inertia
  subgroup of `Gal(F^sep/F)` in `SeparableClosure F`.
- KP's extension `L/K` is an intermediate field of `F^sep/K`
  (`IntermediateField (UnramifiedClosure F) (SeparableClosure F)`), finite
  and Galois over `K`. Its valuation is `intermediateValuation F L`, the
  restriction to `L` of the published `LocalGalois.Separable.sepClosureValuation F`.
  That valuation is the spectral valuation of `F^sep`, the unique extension
  of the valuation of `F` because `F` is complete. Its restriction to `L` is
  therefore the unique valuation extending that of `K` (KP Lemma 2.5.6).
- The norm is the published `GaloisPointComparison.rationalNorm K L T :
  T_L(L) →* T(K)` for a commutative affine `K`-group scheme `T`. The
  published `rationalExtend_norm` shows that after extension to `T(L)` it is
  the product of the Galois conjugates. This is KP's norm map `T(L) → T(K)`.
- Base change along a field extension is the published
  `GaloisPointComparison.baseChanged`, and `rationalExtend k L G : G(k) →*
  G_L(L)` is the map on rational points.

## Declarations

### Over an arbitrary field

- `characterValuationKernel v G : Subgroup (rationalPoints G)` is
  `{g | v(χ(g)) = 1 for every χ ∈ X^*_k(G)}`, the intersection over the
  rational characters of the kernels of `g ↦ v(χ(g))`. Laws:
  `mem_characterValuationKernel` and the instance
  `characterValuationKernel_normal`. For a `k`-torus `T` the rational
  characters are `X^*(T)^Θ`, so this is the second description of `T(k)^b` in
  Proposition 2.5.8. It is used only for the split torus `T_L` over `L`, where
  `X^*(T_L)^Θ = X^*(T_L)` and the second and third descriptions agree.
- `simplyConnectedImage d π : Subgroup (rationalPoints G)` is the range of
  `rationalPoints.map (π ≫ d) : C(k) → G(k)`, with `mem_simplyConnectedImage`.
  Under `IsSimplyConnectedDerivedCover d π` it is KP's `G(k)^♮`
  (Definition 2.6.20).
- `IsMaximallySplitMaximalTorus i`, for `i : T → G`, says that `i` is a
  maximal torus (`IsMaximalTorus i`) and that some maximal split torus
  `a : A → G` of `G` factors as `a = f ≫ i` through `T`. This is
  Definition 2.6.2 in an equivalent form. If the maximal split subtorus `S_T`
  of `T` is a maximal split torus of `G`, take `A = S_T`. Conversely, if a
  maximal split torus `A` of `G` lies in `T`, then `A ⊆ S_T`, and `S_T` is a
  split torus of `G`, so `A = S_T` by maximality. The Library has no maximal
  split subtorus of a torus, so this equivalence is not proved.

### The norm image

- `baseChange_toGrp` (by `rfl`): the group scheme underlying the commutative
  base change `T_L` used by `rationalNorm` is `baseChanged K L T.toGrp`. So the
  splitting condition below and the norm refer to the same `T_L`.
- `torusNormIwahori K L v T : Subgroup (rationalPoints T.toGrp)` is the image
  of `characterValuationKernel v T_L` under `rationalNorm K L T`, with
  `mem_torusNormIwahori`. When `L` splits `T` and `v` is the valuation of `L`
  extending that of `K`, this is `T(K)^0` of Definition 2.5.13.

### Over `F` and `K`

- `UnramifiedClosure F` is `K`. `intermediateValuation F L` is the valuation
  of `L` described above, with `intermediateValuation_apply`.
- `UnramifiedZeroDatum F H`, for a `K`-group `H`, holds the data of
  Definition 2.6.23(1) for `H`:
  - a commutative affine `K`-group scheme `T` with `i : T → H` and
    `IsMaximallySplitMaximalTorus i`;
  - an intermediate field `L` of `F^sep/K`, finite and Galois over `K`, with
    `IsSplitTorus (baseChanged K L T.toGrp)`;
  - `d : D → H`, `π : C → D` with `IsSimplyConnectedDerivedCover d π`.

  Definition 2.6.23(1) needs `H` quasi-split. Every connected reductive
  `K`-group is quasi-split by Corollary 2.3.8, so no quasi-splitness field is
  needed. That `H` is connected reductive is part of
  `IsSimplyConnectedDerivedCover`. For `E : UnramifiedZeroDatum F H`:
  - `E.torusIwahori` is `T(K)^0 = torusNormIwahori K L (intermediateValuation F L) T`;
  - `E.simplyConnectedImage` is `H(K)^♮`;
  - `E.zeroPoints = E.simplyConnectedImage ⊔ i(E.torusIwahori)` is
    `H(K)^0 = H(K)^♮ · T(K)^0`, with `simplyConnectedImage_le_zeroPoints` and
    `map_torusIwahori_le_zeroPoints`.
- `anisotropicZeroPoints E`, for an `F`-group `M` and
  `E : UnramifiedZeroDatum F M_K`, is the preimage of `E.zeroPoints` under
  `rationalExtend F K M : M(F) → M(K)`, with `mem_anisotropicZeroPoints`.
  With `M(F)` viewed as a subgroup of `M(K)` this is
  `M(F)^0 = M(K)^0 ∩ M(F)` of Definition 2.6.23(2). That part of KP's
  definition applies when `M/Z(M)` is anisotropic. This is not a hypothesis
  of `anisotropicZeroPoints`, which is used below only for `M = Z_G(S)`.
- `ZeroSubgroupDatum i j`, for `i : S → G` and `j : Z → G`, holds the data of
  Definition 2.6.23(3) for `G`, with `M_0 = Z_G(S)`:
  - `IsMaximalSplitTorus i`;
  - `(torusCentralizer i).IsRepresentedBy j`, so `Z` is the centralizer of
    `S`, a minimal Levi subgroup;
  - `centralizerDatum : UnramifiedZeroDatum F Z_K`, the data of part (1) for
    `Z_K`;
  - `d : D → G`, `π : C → D` with `IsSimplyConnectedDerivedCover d π`.

  For `E : ZeroSubgroupDatum i j`:
  - `E.centralizerZero = anisotropicZeroPoints E.centralizerDatum` is
    `Z(F)^0 = Z(K)^0 ∩ Z(F)`;
  - `E.simplyConnectedImage` is `G(F)^♮`;
  - `E.zeroSubgroup = E.simplyConnectedImage ⊔ j(E.centralizerZero)` is
    `G(F)^0 = G(F)^♮ · M_0(F)^0`, with `simplyConnectedImage_le_zeroSubgroup`
    and `map_centralizerZero_le_zeroSubgroup`.

## Conventions and derived choices

- Which part of Definition 2.6.23 is used. Part (1) is used only over `K`.
  Part (2) is used only for `Z = Z_G(S)`, which is anisotropic modulo its
  center. Part (3) is used for `G`. So `zeroSubgroup` always follows part (3).
  By Remark 2.6.25 the parts agree where they overlap. When `G` is
  quasi-split, `Z_G(S)` is a maximally split maximal torus and (3) is (1). When
  `G/Z(G)` is anisotropic, `Z_G(S) = G` and (3) reduces to (2). This
  agreement is not proved here.
- Minimal Levi subgroups. KP's part (3) chooses a minimal Levi subgroup
  `M_0`. The minimal Levi subgroups of `G` are the centralizers `Z_G(S)` of
  maximal split tori (proof of Fact 2.6.22). Here `M_0` is the closed subgroup
  `j : Z → G` representing the actual centralizer of `S`.
- Joins. KP write `G(k)^♮ · T(k)^0` and `G(k)^♮ · M_0(k)^0` as products of
  subgroups. They are subgroups because `G(k)^♮` is normal in `G(k)`
  (proof of Lemma 2.6.24). Here they are the joins `⊔`, the subgroups
  generated. The join equals the product set once `G(k)^♮` is normal. That
  normality is not proved.
- `M(F)` inside `M(K)`. KP's intersection `M(K)^0 ∩ M(F)` is the preimage
  under the extension map `rationalExtend F K M`.
- The splitting field lies in the fixed separable closure `F^sep`, as in KP,
  where `K` and `L` are subfields of `k^s`.

## What is not proved or defined

- Existence. Neither `UnramifiedZeroDatum F H` nor `ZeroSubgroupDatum i j` is
  a typeclass. Nothing says either type is inhabited: not the existence of a
  maximally split maximal torus, of a finite Galois splitting field in
  `F^sep`, of a simply connected cover, or of a closed subgroup representing
  `Z_G(S)`.
- Independence of the choices: of `L` (Lemma 2.5.12), and of `T` and `M_0`
  (Lemma 2.6.24). Also independence of the chosen cover.
- That `G(k)^♮` is normal, and that `G(k)^0` is normal and open
  (Lemma 2.6.24). Openness of `T(K)^0` (Lemma 2.5.12). No topology on the
  rational points is used.
- Fact 2.6.21 (functoriality of `G(k)^♮`) and Fact 2.6.22
  (`G(k) = G(k)^♮ · M(k)`).
- `T(k)^0 ⊆ T(k)^1` with finite index (Lemma 2.5.14), and
  `G(k)^0 ⊆ G(k)^1` with finite index (Lemma 2.6.29).
- `G(k)^0 = G(K)^0 ∩ G(k)` (Remark 2.6.26, Proposition 9.3.24), and the
  agreement of the parts of Definition 2.6.23 (Remark 2.6.25).
- The equivalence of `IsMaximallySplitMaximalTorus` with Definition 2.6.2 as
  stated, which needs the maximal split subtorus of a torus.
- `T(k)^0 = T(K)^0 ∩ T(k)` of Definition 2.5.13 for a `k`-torus `T` is not
  defined separately. By Remark 2.6.25(1) it agrees with
  `anisotropicZeroPoints` for `M = T`, whose `H(K)^♮` is trivial. This is not
  proved.
- `G(k)^1` is the published `Plancherel.rationalCommonNormKernel G`, used in
  `KPParahoric`. It is not redefined here.
