# The doubled-root commutator estimate over `K = F^ur`: the `Z`-component lies in `Z(K)_{2r}`

Lean module: `Langlands.Geometry.Building.KPLocalDoubleRootCommutatorStatement`.
Declaration: `Langlands.Geometry.Building.KPLocalDoubleRootCommutatorStatement : Prop`
(universe parameter `u`).

This is a statement only. Nothing here proves it, and no other Library result is claimed to
imply it.

## Setting and binders

The statement quantifies over:

- a nonarchimedean local field `F : Type u` (`Field`, `ValuativeRel`, `TopologicalSpace`,
  `IsNonarchimedeanLocalField`), in any universe `u` and any characteristic;
- `K = UnramifiedClosure F`, the Library's maximal unramified extension of `F`;
- an affine group scheme `H` over `Spec K` (`[IsAffineHom H.X.hom]`) and building data
  `B : MaximalUnramified.BuildingData F H`, that is
  `IntegerValuationBuildingData (MaximalUnramified.valuation F) H`. These are a connected
  reductive group `G = H` over `K`, a maximal `K`-split torus `S` (`B.i`), the actual
  centralizer `Z = Z_G(S)` (`B.centralizer`), and the ω-compatible equipollence class of
  valuations of the root datum (`B.apartment`, KP Axiom V 6);
- `hZ : IsTorus B.centralizer.Z`. This is the binder convention of the published module
  `Langlands.Geometry.Building.KPLocalMoyPrasadGroups`: `B.centralizerTorus hZ` is `Z`
  viewed as a commutative group scheme, and
  `B.centralizerTorusFiltration hZ r = localTorusFiltration F (B.centralizerTorus hZ) hZ r`
  is KP's `Z(K)_r` (§7.2). These definitions are used unchanged. Over `K = F^ur` every
  connected reductive group is quasi-split, so `Z = T` is a maximal torus (KP §7.2: "When G
  is quasi-split, then Z = T is a maximal torus").

There are no further premises: no supplied filtration, no apartment axioms, and none of the
conclusions of KP Lemma 7.2.3 or Proposition 13.2.5 (normality, Iwahori factorization,
intersection with `Z`) are assumed.

## Statement

For all such `F`, `H`, `B`, `hZ`, every point `x : B.Apartment` (a valuation `φ = x.val` in
the class `A(S)`), every relative root `a : relativeRoots B.i` and all `u u' : G(K)`
(`rationalPoints H`), suppose that

1. `u ∈ U_a(K)` (`B.rootGroup a`), `u ≠ 1`, `u' ∈ U_{-a}(K)` (`B.rootGroup (-a)`),
   `u' ≠ 1`;
2. `u ∈ U_{2a}(K)` **or** `u' ∈ U_{-2a}(K)`, written
   `u ∈ B.doubleRootGroup a ∨ u' ∈ B.doubleRootGroup (-a)`. By the Library definition
   `doubleRootGroupPoints`, `B.doubleRootGroup b` is the root group of `2 • b` when `2 • b`
   is a relative root and the trivial subgroup otherwise (KP's convention
   `U_{2a}(K) = {1}`). Both doubled inputs are included; neither is required;
3. `r : ℝ≥0`, `0 < r` and `r = x.val a u + x.val (-a) u'` in `WithTop ℝ`, that is
   `r = φ_a(u) + φ_{-a}(u')` in KP's notation;
4. `v', v : G(K)`, `z : Z(K)` (`rationalPoints B.centralizer.Z`), `v' ∈ U_{-a}(K)`,
   `v ∈ U_a(K)` and `u'⁻¹ u u' u⁻¹ = v' · j(z) · v`, where `j = B.centralizer.j`.

Then `z ∈ B.centralizerTorusFiltration hZ (2 * r)`, i.e. `z ∈ Z(K)_{2r}`.

**Quantifier scope.** All binders are universal; nothing is chosen. The point `x`, the root
`a` and the elements `u`, `u'` come first, then the doubled-input disjunction, then `r`
(which is determined by `x`, `u`, `u'` through hypothesis 3), and finally every
factorization `v' · j(z) · v` of the commutator. The statement does not assert that such a
factorization exists (KP prove existence for `r > 0` in Proposition 7.1.1). It constrains
`z` whenever one is given. The `z` of a factorization is unique, because
`U_{-a}(K) ∩ Z(K) U_a(K) = {1}` (KP, proof of Proposition 7.1.1(1)); it is the
`Z`-component of the commutator of `u'⁻¹` and `u` in KP's Definition 7.1.3.

**When the doubled hypothesis can hold.** If `2a` is not a relative root then `2(-a)` is not
one either (the relative roots are symmetric), both doubled groups are trivial, and
hypothesis 2 contradicts `u ≠ 1`, `u' ≠ 1`. So the statement has content only for
multipliable roots `a` (`2a` a root), and in particular only for groups whose relative root
system has a `BC` component. For a divisible root `a = 2b`, `2a = 4b` is not a root.

**The factor `2`.** Hypotheses 1, 3, 4 are exactly those of
`ParahoricBuildingData.CentralizerFiltration.IsCommutatorFriendly` (KP Definition 7.2.1),
whose conclusion is depth `r`. With a doubled input the actual `Z`-component is twice as
deep. The computation below gives `ω(γ - 1) = 2r` exactly, so `2r` is the sharp index for
the rank-one coordinate `γ`. The statement asserts only membership in `Z(K)_{2r}`.

**Comparison with existing statements.**

- The hypotheses copy those of
  `ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly` (module
  `Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement`), with the `K`-level data
  `B` in place of supplied data `P` over `F`, and the published filtration
  `B.centralizerTorusFiltration hZ (2 * r)` in place of a supplied `Zf.filtration (2 * r)`.
  This statement is the `K`-level analogue of that predicate for the actual filtration.
- `KPLocalCorootComponentStatement` (same hypotheses without the doubled disjunction)
  produces an induced torus `T_a`, a morphism `f : T_a → Z` and `c` with `f(c) = z`
  congruent to `1` at depth `r`. Its conclusion is only at depth `r`, so it does not imply
  this statement.

## Provenance and mathematical content

KP do not state this estimate as a separate result. It is the doubled case of the
computation in the proof of Proposition 7.1.1 for quasi-split `G` (printed pp. 239–240), as
used in the proof of Lemma 7.2.3 (printed p. 246): "one can argue as in that proof (using
the functoriality of the filtration) and reduce to computations in SL2 and SU3 ... the
element γ computed there is the Z-component of the commutator and has the desired
property". The statement records the sharper property of `γ` when a doubled input is
present. The derivation below is the expected proof route. It is not formalized here.

**Reduction to `SU_3`.** The commutator of `u ∈ U_a(K)` and `u' ∈ U_{-a}(K)` is computed in
the simply connected cover `G_a` of the `K`-rank-one group generated by `U_{±a}` and
`U_{±2a}`. For multipliable `a`, `G_a = R_{L/K} SU_3`, where `SU_3` is the quasi-split
special unitary group of a separable quadratic extension `L'/L` and `L/K` is finite
separable. KP may replace `φ` by an equipollent valuation; this does not change
`r = φ_a(u) + φ_{-a}(u')`, because the translation parts cancel.

**The `SU_3` computation** (KP p. 239, PDF p. 270). With `u = u_a(α, β)` and
`u' = u_{-a}(α', β')`, KP compute `u u' = x' · diag(γ, γ̄γ⁻¹, γ̄⁻¹) · x` with
`x' ∈ U_{-a}`, `x ∈ U_a` and

`γ = 1 + αα' + ββ'`.

Then `u'⁻¹ u u' u⁻¹ = (u'⁻¹ x') · z · (x u⁻¹)` with `z = diag(γ, γ̄γ⁻¹, γ̄⁻¹)`, so `z` is the
`Z`-component (Definition 7.1.3).

- If `u ∈ U_{2a}(K)` then `u = u_a(0, β)`, so `α = 0` (KP p. 239 makes exactly this
  simplification for the second point of Proposition 7.1.1(2)).
- If `u' ∈ U_{-2a}(K)` then `u' = u_{-a}(0, β')`, so `α' = 0`.

In either case `αα' = 0` and `γ - 1 = ββ'`. KP's root valuations (3.2.3) and (3.2.7)
(printed pp. 149–151) are `φ_a(u_a(α, β)) = ½(ω(β) - μ)` and
`φ_{-a}(u_{-a}(α', β')) = ½(ω(β') + μ)`, so

`r = φ_a(u) + φ_{-a}(u') = (ω(β) + ω(β')) / 2`, hence `ω(γ - 1) = ω(β) + ω(β') = 2r`.

Without a doubled input only `ω(αα') ≥ r` is available (from `2ω(α) ≥ ω(β)`,
`2ω(α') ≥ ω(β')`), which is why the ordinary estimate stops at `r`.

**From `γ` to `Z(K)_{2r}`** (KP Definition 7.2.2, properties (1), (2), Lemma 7.2.3,
printed pp. 245–246). Let `T_a = R_{L'/K} G_m`, an induced torus, with the coroot
`f : T_a → Z`, `γ ↦ diag(γ, γ̄γ⁻¹, γ̄⁻¹)` followed by `G_a → G`. Then `z = f(γ)`.

- *Congruence criterion for induced tori* (property (2); Library
  `mem_localTorusFiltration_of_induced` in `KPLocalTorusCharacterFiltration`): for `r > 0`,
  `T_a(K)_{2r}` consists of the `t` with `ω(χ(t) - 1) ≥ 2r` for every character `χ` of
  `T_a` over `Ω = SeparableClosure F`. The characters are products of `σ(γ)^{±1}` for the
  `K`-embeddings `σ : L' → Ω`. The valuation of `K` extends uniquely to `Ω`, so
  `ω(σ(γ) - 1) = ω(γ - 1) = 2r`, and `{y : ω(y - 1) ≥ 2r}` is a group because `2r > 0`.
  Hence `γ ∈ T_a(K)_{2r}`.
- *Functoriality* (Definition 7.2.2; Library `map_localTorusFiltration_le`): `f` maps
  `T_a(K)_{2r}` into `Z(K)_{2r} = B.centralizerTorusFiltration hZ (2 * r)`.

So `z = f(γ) ∈ Z(K)_{2r}`.

## Why this is a separate statement

The parent proof of `LocalMoyPrasadGroupPropertiesStatement` (Task 6191) needs this estimate
already for its clause 1 (normality of `G(K)_{x,r}`): a depth-zero element of `U_a`
conjugating a depth-`r` element of `U_{-2a}` produces a middle coordinate that must lie at
full depth `r`, whereas commutator friendliness applied to `U_a` versus `U_{-a}` gives only
`r/2`. Deriving the doubled estimate from normality, Iwahori factorization and the
intersection with `Z` would therefore be circular as the sole route. For supplied
filtrations the doubled premise is not automatic; see
`notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md`. That counterexample
concerns supplied filtrations and does not bear on the actual filtration here.

## Notes for a proof (not part of the statement)

- A proof must identify the class `B.apartment` with the Chevalley–Steinberg class of the
  rank-one group `G_a`, and identify the actual `SU_3` coordinates and coroot inside `G`.
  The Library has `OmegaCompatibleApartmentUniquenessProof`, `IntegerOmegaApartmentRigidity`,
  `QuasiSplitApartmentAssembly`, `RootUnitaryCoordinates`,
  `QuasiSplitR2RootUnitaryCoordinatesStatement` and `QuasiSplitMultipliableFactorization`.
  This unit does not check which of these are proved.
- The rank-one coordinate comparison is the same one a proof of
  `KPLocalCorootComponentStatement` (Task 6192) needs; the doubled case only sharpens the
  final valuation estimate.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), literature id
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  - Proposition 7.1.1 and its proof for quasi-split `G` (the `SL_2` and `SU_3` computations
    and the `α = 0` simplification for `u ∈ U_{2a}(k)`), printed pp. 237–240 (PDF
    pp. 268–271);
  - Definition 7.1.3 (the `Z`-component), printed p. 242 (PDF p. 273);
  - §7.2, Definitions 7.2.1 and 7.2.2 with properties (1) and (2), Lemma 7.2.3 and its
    proof, printed pp. 245–246 (PDF pp. 276–277);
  - §3.2, the `SU_3` root valuations (3.2.3) and (3.2.7), printed pp. 149–151 (PDF
    pp. 180–182).
- Kaletha–Prasad, *Corrections and additions* (2024), literature id
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p. 33
  (Chapter 7). These corrections add hypothesis AS 5, correct the proof of Lemma 7.1.4 and
  add Proposition 7.3.12(6). None of them changes the rank-one computation in the proof of
  Proposition 7.1.1, Definition 7.1.3 or Lemma 7.2.3.
