# The reflections `m(u)` and Axiom 4.1.8 (2), (3) of Kaletha–Prasad

Module `Langlands.Geometry.Building.ParahoricBuildingAxioms`, namespaces
`Langlands.Geometry.Building.ValuationBuildingData`,
`Langlands.Geometry.Building.ParahoricBuildingData` and
`Langlands.Geometry.Building.PartiallyValidParahoricBuildingData`.

The published module `ValuationBuildingAxioms` states on building data
`B : ValuationBuildingData G` the clauses of the corrected KP Definition 4.1.26 that can be written
with the objects of `B` alone. Its list of clauses that are not included names AS 1, the
`m(u)`-form of AS 2, and Axiom 4.1.8 (2) and (3). These needed the elements `m(u)` of KP
Proposition 2.11.17 and the groups `G(k)^0` and `Z(k)^0`. Both are now in the Library:

- `RelativeRoot.IsOppositeFactorPair` and the statement `RootRankOneFactorizationStatement` of KP
  Proposition 2.11.17 (module `Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement`);
- `ParahoricBuildingData G` (Worker 1238's module `KPParahoric`), which extends
  `ValuationBuildingData G` by the data that define `Z(F)^0` and `G(F)^0` (module
  `KPZeroSubgroups`).

This module states these clauses. It also defines one predicate that bundles every clause of
Definition 4.1.26 now stated in the Library, and the type of building data that satisfy it.

All predicates here are conditions on given data. Nothing in this module asserts that they hold
for any data, or that data exist; that is KP's construction (Chapters 6, 7 and 9). The bundle is
strictly weaker than Definition 4.1.26 (section "Not included").

## Setting

- `F` is a field with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, and
  `G : GroupScheme (Spec (CommRingCat.of F))` with `[IsAffineHom G.X.hom]`. `G(F)` is
  `rationalPoints G`, with the group structure from the scoped `MonObj` instances.
- `B : ValuationBuildingData G`, with maximal split torus `B.i : S → G`, the class
  `B.apartment` of valuations `A(S)`, the apartment `B.Apartment` (an affine space over
  `TranslationSpace B.i`, KP's `V′`), the relative roots `relativeRoots B.i` (KP's `Φ`), the
  root groups `B.rootGroup α` (`U_a(F)`), and `N(F) = normalizerPoints B.i`. A point `x` of the
  apartment is a valuation of the root datum, and `x.val α u ∈ ℝ ∪ {∞}` is KP's `x_a(u)`.
- `rootForm B.i α` is the linear form on `TranslationSpace B.i` given by the root `α`.
- `B.affineRootGroup α ψ` is KP's `U_ψ` and `B.apartment.affineRootGroupPlus α ψ` is `U_{ψ+}`
  (KP Definition 6.3.1). `B.apartment.extendedAffineRoots` is KP's `Ψ′` and `B.affineRoots` is
  KP's `Ψ` (Definition 6.3.4).
- `P : ParahoricBuildingData G`. Besides the fields of `ValuationBuildingData`, it gives
  `P.zeroSubgroup` (KP's `G(F)^0`, Definition 2.6.23 (3)), `P.centralizerZero` (KP's `Z(F)^0` as
  a subgroup of `Z(F)`, Definition 2.6.23 (2)) with `P.centralizer.j : Z → G`, and
  `P.parahoric Ω = Z(F)^0 · G(F)^♯_Ω` (KP Definition 7.4.1 (4)).

## Values of root elements

Three lemmas about the valuations of the class `A(S)`, used below.

- `val_apply_eq_add` (proved): `y_a(u) = x_a(u) + a(y − x)` for points `x, y` of the apartment.
  This is KP's translation action `φ_{v,a}(u) = φ_a(u) + a(v)` (§6.1, before Lemma 6.1.6, book
  PDF p. 231, printed p. 200), from the published `KPApartmentData.val_mk_vadd`.
- `val_apply_one` and `val_apply_ne_top` (proved): `x_a(1) = ∞`, and `x_a(u) ≠ ∞` for
  `u ∈ U_a(F)`, `u ≠ 1` (axiom V 1 of KP Definition 6.1.2).

## The elements `m(u)`

KP Axiom 4.1.6 (book PDF p. 190, printed p. 159): "Given `a ∈ Φ` and `u ∈ U_a(k)^*` the elements
`u′, u″ ∈ U_{−a}(k)^*` and `m(u) = u′ · u · u″ ∈ N(k)` are as in Proposition 2.11.17."
Proposition 2.11.17 (book PDF p. 167, printed p. 136): "Given `u ∈ U_a(k)^* = U_a(k) − {1}`,
there exist unique `u′, u″ ∈ U_{−a}(k)` such that the element `m(u) = u′uu″ ∈ G(k)` normalizes
`S`."

- The published `RelativeRoot.IsOppositeFactorPair B.i a u p` says that `p = (u′, u″)` has
  both entries in `U_{−a}(F)` and `u′ u u″ ∈ N(F)`.
- `B.reflectionElement hp : normalizerPoints B.i` is `m(u) = u′ u u″` for such a pair `hp`
  (`coe_reflectionElement`).
- `exists_isOppositeFactorPair` (proved from a hypothesis): if
  `RootRankOneFactorizationStatement` holds, then every `u ∈ U_a(F)`, `u ≠ 1`, has an opposite
  factor pair. The statement is published but not proved in the Library, so it is a hypothesis
  of this lemma.

## The hyperplanes `H_u` and the functionals `ψ^u_a`

KP §6.2 (book PDF p. 243, printed p. 212), for an equipollence class `A` of valuations: "For
`u ∈ U_a(k)^*`, the subset `H_u = {φ ∈ A | φ_a(u) = 0} ⊂ A` is immediately seen to be a
hyperplane with derivative `a^⊥ ⊂ V(S′)`."

- `B.reflectionHyperplane α u` is the set `{x | x.val α u = 0}`. This is KP's `H_u` verbatim.
- `B.reflectionFunctional α u : B.Apartment →ᵃ[ℝ] ℝ` is KP's `ψ^u_a`. It is the published
  `B.apartment.affineFunctional α x₀ c`: the affine functional with linear part `rootForm B.i α`
  and value `c` at a base point `x₀` (an arbitrary point of the apartment). Here
  `c = x₀_a(u)` when this is finite, and `c = 0` otherwise. The value `0` is only a convention
  for `u = 1`, where `ψ^u_a` is not used.
- `reflectionFunctional_linear` (proved): the derivative of `ψ^u_a` is `a`.
- `coe_reflectionFunctional_apply` (proved): `ψ^u_a(x) = x_a(u)` for every `x` when
  `u ∈ U_a(F)`, `u ≠ 1`. So the definition does not depend on the base point.
- `reflectionHyperplane_eq` (proved): for such `u`, `H_u` is the zero set of `ψ^u_a`.

Derived definition. KP's AS 2 defines `ψ^u_a` as "the unique functional with derivative `a` that
vanishes on `H_u`", where AS 1 only says that `m(u)` fixes some hyperplane `H_u`. Here `ψ^u_a` is
defined as the functional `x ↦ x_a(u)`, and `H_u` as its zero set, as in KP §6.2. For valuations
this is the only choice compatible with AS 3: the corrected AS 3 below holds for this `ψ^u_a`
and the data's `U_ψ` (KP Definition 6.3.1). By that lemma, for `u ≠ 1`, `x ↦ x_a(u)` is the
largest `ψ` with derivative `a` and `u ∈ U_ψ`, so AS 3 determines `ψ^u_a`. KP also note after Definition 6.3.4 that `u ∈ U_ψ − U_{ψ+}` if and only if
`H_ψ = H_u`.

## AS 1

AS 1 (book PDF p. 190, printed p. 159): "The action of `m(u)` on `A` fixes a hyperplane `H_u`
that is an affine subspace of `A` under the vector subspace `ker(a)`."

`B.HasRootReflections : Prop` is the condition: for every `a ∈ Φ`, every `u ∈ U_a(F)` with
`u ≠ 1`, every opposite factor pair `(u′, u″)` of `u` and every `x ∈ H_u`,
`m(u) • x = x`. Here `•` is the published action of `N(F)` on the apartment.

Derived formulation.

- The hyperplane is KP's `H_u = {x_a(u) = 0}` of §6.2. It is an affine hyperplane with
  direction `ker(a)`, since `ψ^u_a` has linear part `a`. This is not restated in Lean.
- The condition is asked for every opposite factor pair. By the uniqueness in KP
  Proposition 2.11.17 there is exactly one pair, so this is KP's `m(u)`. The Library does not
  prove the uniqueness. If `u` has no pair, then the condition is empty for `u`. With
  `RootRankOneFactorizationStatement`, `exists_isOppositeFactorPair` gives a pair for every such
  `u`.
- For valuations, KP prove AS 1 in Proposition 6.2.1 (book PDF p. 243, printed p. 212):
  "`φ − m(u)φ = φ_a(u) a^∨`". So `m(u)` is the affine reflection along `H_u`. Here AS 1 is a
  condition, because the action of `m(u)` on the apartment is only given abstractly by the data.

## AS 2 and AS 3 in terms of `ψ^u_a`

AS 2 (book PDF p. 190): "`Ψ′ = {ψ^u_a | a ∈ Φ, u ∈ U_a(k)^*}` is an affine root system with
derivative `Φ`." AS 3 (book PDF p. 191, printed p. 160) defines
`U_ψ = {u ∈ U_a(k)^* | ψ^u_a ≥ ψ}` and `U_{ψ+} = {u ∈ U_a(k)^* | ψ^u_a > ψ}`. The corrections
(PDF p. 27) add `∪ {1}` to both definitions.

- `B.reflectionAffineRoots` is the set `{ψ^u_a | a ∈ Φ, u ∈ U_a(F), u ≠ 1}` of AS 2.
- `reflectionAffineRoots_eq` (proved): this set is the published `Ψ′ = extendedAffineRoots`, the
  set of `ψ` with derivative in `Φ` and `U_{ψ+} ≠ U_ψ`. This is KP Remark 4.1.7 ("we recover
  `Ψ′` as `{ψ ∈ A^* | a = ψ̇ ∈ Φ, U_{ψ+} ⊊ U_ψ}`") and Definition 6.3.4. Proof. If
  `ψ = ψ^u_a`, then `u ∈ U_ψ` and `u ∉ U_{ψ+}`, by `coe_reflectionFunctional_apply`. Conversely,
  an element `u ∈ U_ψ − U_{ψ+}` satisfies `x_a(u) = ψ(x)` at a point `x`. So `u ≠ 1`, and
  `ψ = ψ^u_a`, because both have derivative `a` and agree at `x`.
- `SatisfiesApartmentAxioms.isAffineRootSystem_reflectionAffineRoots` (proved): under the
  published `B.SatisfiesApartmentAxioms`, the set `{ψ^u_a}` is an affine root system
  (`IsAffineRootSystemWithRankZero`) with derivative set `Set.range (rootForm B.i)`, which is `Φ`.
  By the previous lemma this is the published AS 2 field. So AS 2 in its `m(u)`-form is not a new
  condition.
- `mem_affineRootGroup_iff_reflectionFunctional` (proved): for `ψ` with derivative `a`,
  `u ∈ U_ψ` if and only if `u = 1`, or `u ∈ U_a(F)`, `u ≠ 1` and `ψ ≤ ψ^u_a`.
- `mem_affineRootGroupPlus_iff_reflectionFunctional` (proved): the same for `U_{ψ+}` with
  `ψ < ψ^u_a` pointwise.

These two lemmas are the corrected AS 3 for the data's `U_ψ` and `U_{ψ+}`. The published AS 3
field of `SatisfiesApartmentAxioms` asks that `Ψ` be an affine root system.

## Bounded subsets

`B.IsBoundedSubset Ω` for `Ω ⊆ A` means: every affine functional `f : A → ℝ` is bounded above on
`Ω`.

Derived definition. KP use bounded subsets of an apartment for its Euclidean metric. Applying the
condition to `f` and `−f` bounds every affine functional on `Ω`. In the finite-dimensional affine
space `A`, this is equivalent to metric boundedness. That equivalence is not proved here, and no
metric on `A` is used.

## `U_{a,Ω,0}` and the affine root groups

The published `B.rootFixer α Ω` is KP's `U_{a,Ω,0} = ⋂_{x ∈ Ω} U_{a,x,0}` (Definition
7.4.1 (1)).

- `affineRootGroup_le_rootFixer` (proved): if `ψ` has derivative `a` and `ψ ≥ 0` on `Ω`, then
  `U_ψ ⊆ U_{a,Ω,0}`. Indeed `U_ψ = U_{a,x,ψ(x)} ⊆ U_{a,x,0}` for `x ∈ Ω`.
- `rootFixer_eq_affineRootGroup_of_isLeast` (proved): let `ψ` have derivative `a`, let `ψ ≥ 0`
  on `Ω`, and let `ψ ≤ ψ′` for every `ψ′ ∈ Ψ′` with derivative `a` and `ψ′ ≥ 0` on `Ω` (hypothesis
  `hleast`). Then `U_{a,Ω,0} = U_ψ`. Proof. One inclusion is the previous lemma. For `u ≠ 1` in
  `U_{a,Ω,0}`, the functional `ψ^u_a` lies in `Ψ′`, has derivative `a`, and is `≥ 0` on `Ω`. So
  `ψ ≤ ψ^u_a` by `hleast`, and `u ∈ U_ψ` by the corrected AS 3.

The smallest element of `Ψ′` with derivative `a` that is non-negative on `Ω`, as in Axiom
4.1.8 (3), satisfies the hypotheses on `ψ`. KP use Proposition 6.3.7 (the set `Ψ′_a` has no
accumulation point) for such existence statements (Remark 6.3.17, book PDF pp. 252–253, printed
pp. 221–222, for `Ψ`). That proposition is not in the Library, so the lemma takes `ψ` with
these properties as input and does not assert that one exists.

## `G(F)^0_Ω`

KP §4.1, before Axiom 4.1.8 (book PDF p. 191, printed p. 160): "Given a non-empty bounded subset
`Ω` of an apartment `A` of `B(G)`, […] let `G(k)^0_Ω` denote the subgroup of `G(k)^0` consisting
of elements that fix `Ω` pointwise."

- `P.zeroFixer Ω` is `P.zeroSubgroup ⊓ P.pointwiseFixer (P.apartmentMap '' Ω)`: the elements of
  `G(F)^0` that fix the image of `Ω` in the building `P.ReducedBuilding` pointwise.
- `mem_zeroFixer` (proved): `g ∈ G(F)^0_Ω` if and only if `g ∈ G(F)^0` and
  `g • [1, x] = [1, x]` for all `x ∈ Ω`.

The definition is made for every `Ω ⊆ A`. KP use it only for non-empty bounded `Ω`, and the
axioms below assume this.

KP use the notation `G(k)^0_Ω` also for the group `Z(k)^0 · G(k)^♯_Ω` of Definition 7.4.1 (4),
which is the published `P.parahoric Ω`. These are two different definitions, and this module
keeps them apart. KP Proposition 7.6.4 (1) (book PDF p. 296, printed p. 265) shows for their
construction that the two agree when `Ω` lies in a facet ("the group `G(k)^0_Ω` is the
stabilizer, as well as the pointwise stabilizer, of `Ω` in `G(k)^0`"), and refers to
Proposition 7.7.5 for general `Ω`. Neither proposition is stated here. The only relation proved
here is `HasZeroFixerGenerators.zeroFixer_le_parahoric` below.

## Axiom 4.1.8 (2)

Axiom 4.1.8 (2) (book PDF p. 191, printed p. 160): "Given `Ω ⊂ A`, the group `G(k)^0_Ω` is
generated by `Z(k)^0` and `U_ψ` for all `ψ ∈ Ψ` with `ψ(Ω) ⊂ ℝ_{≥0}`." The corrections (PDF
p. 27): "In Axiom 4.1.8(2), it should be emphasized that `Ω` is assumed non-empty and bounded."

- `P.nonnegativeRootSubgroup Ω` is the subgroup of `G(F)` generated by the image of `Z(F)^0`
  under `j : Z → G` and by the groups `U_ψ` for `ψ ∈ Ψ = P.affineRoots` with derivative a relative
  root `α` and `ψ ≥ 0` on `Ω`. Every `ψ ∈ Ψ` has such a derivative, so these are the generators of
  the axiom.
- `nonnegativeRootSubgroup_le_parahoric` (proved): this subgroup lies in `P_Ω = P.parahoric Ω`.
  The generators `U_ψ` lie in `U_{a,Ω,0}` (`affineRootGroup_le_rootFixer`), hence in
  `G(F)^♯_Ω`.
- `P.HasZeroFixerGenerators : Prop` is Axiom 4.1.8 (2) with the corrected hypothesis: for every
  non-empty bounded `Ω ⊆ A`, `P.zeroFixer Ω = P.nonnegativeRootSubgroup Ω`.
- `HasZeroFixerGenerators.zeroFixer_le_parahoric` (proved): under the axiom,
  `G(F)^0_Ω ⊆ P_Ω` for non-empty bounded `Ω`.

The axiom is stated with KP's generators `U_ψ`, `ψ ∈ Ψ`, and not as the equation
`P.zeroFixer Ω = P.parahoric Ω`. The generators of `P.parahoric Ω` are the groups `U_{a,Ω,0}`.
Writing them in terms of the `U_ψ`, `ψ ∈ Ψ`, uses the existence of smallest affine roots (Remark
6.3.17), which is not in the Library. So only the inclusion `nonnegativeRootSubgroup_le_parahoric`
is proved.

## Axiom 4.1.8 (3)

Axiom 4.1.8 (3) (book PDF p. 191, printed p. 160): "For `a ∈ Φ`, `U_a(k) ∩ G(k)^0_Ω = U_ψ`, where
`ψ ∈ Ψ′` is the smallest element with derivative `a` that only takes non-negative values on
`Ω`."

- `P.HasRootZeroFixers : Prop` is the condition: for every non-empty bounded `Ω ⊆ A` and every
  `a ∈ Φ`, `U_a(F) ⊓ G(F)^0_Ω = U_{a,Ω,0}` (`P.rootGroup α ⊓ P.zeroFixer Ω = P.rootFixer α Ω`).
- `HasRootZeroFixers.rootGroup_inf_zeroFixer_eq` (proved): under this condition,
  `U_a(F) ⊓ G(F)^0_Ω = U_ψ` for every `ψ` as in `rootFixer_eq_affineRootGroup_of_isLeast`. In
  particular this holds for the smallest `ψ` of the axiom. This is KP's literal form.

Derived formulation. The condition uses `U_{a,Ω,0}` instead of "the smallest `ψ`", so it needs
no existence statement for `ψ`. The previous lemma recovers KP's form whenever the smallest `ψ`
exists. Conversely, when it exists, KP's form implies the condition, by
`rootFixer_eq_affineRootGroup_of_isLeast`. The hypothesis "non-empty and bounded" is the one
under which KP define `G(k)^0_Ω`.

Axiom 4.1.8 (1) is the published `ValuationBuildingData.affineRootGroup_le_pointwiseFixer` (module
`ValuationBuildingAxioms`), proved for all data.

## The bundle of stated clauses

`P.SatisfiesPartialBuildingAxioms : Prop` is a structure with seven fields:

| field | clause of the corrected Definition 4.1.26 |
| --- | --- |
| `apartmentAxioms : P.SatisfiesApartmentAxioms` | V 7, AS 2–AS 5 of Axiom 4.1.6 (V 6 is part of the data) |
| `hasRootReflections : P.HasRootReflections` | AS 1 of Axiom 4.1.6, with the actual `m(u)` |
| `hasCompatibleApartmentFacets : P.HasCompatibleApartmentFacets` | AS 6 of Axiom 4.1.6 |
| `hasNormalizerApartmentStabilizer : P.HasNormalizerApartmentStabilizer` | the clause of Axiom 4.1.1 that the stabilizer of `A(S)` is `N(F)` |
| `hasBoundedOpenStabilizers : P.HasBoundedOpenStabilizers` | Axiom 4.1.2 |
| `hasZeroFixerGenerators : P.HasZeroFixerGenerators` | Axiom 4.1.8 (2) |
| `hasRootZeroFixers : P.HasRootZeroFixers` | Axiom 4.1.8 (3) |

The first five predicates are published in the modules `KPApartmentAxioms` and
`ValuationBuildingAxioms`; their Markdown explains their provenance.

These clauses hold for all data and are not fields:

- Axiom 4.1.4 (A 0) and (A 1): the apartment is an affine space over `TranslationSpace B.i`, and
  the published lemmas `normalizerAction_linear` and `normalizerAction_centralizer` of
  `ValuationBuildingAxioms`.
- Axiom 4.1.8 (1): `affineRootGroup_le_pointwiseFixer` of `ValuationBuildingAxioms`.
- The corrected definitions of `U_ψ` and `U_{ψ+}` in AS 3: the two lemmas of the section on AS 3.

`PartiallyValidParahoricBuildingData G` is the structure that extends `ParahoricBuildingData G`
by one field, `satisfiesPartialBuildingAxioms`. It is the type of building data that satisfy the
bundled clauses. For `P` of this type, the module proves:

- `isAffineRootSystem_reflectionAffineRoots`: `{ψ^u_a}` is an affine root system with derivative
  `Φ`;
- `zeroFixer_le_parahoric`: `G(F)^0_Ω ⊆ P_Ω` for non-empty bounded `Ω`;
- `rootGroup_inf_zeroFixer_eq`: KP's literal Axiom 4.1.8 (3).

The names say "partial" because the bundle does not contain every clause of Definition 4.1.26.
It is not a definition of a Bruhat–Tits building, and no object of this type is constructed.

## Not included

The corrected Definition 4.1.26 (corrections PDF p. 27) asks for Axioms 4.1.1, 4.1.2, 4.1.4,
4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. These parts are not stated in this
module:

- Axiom 4.1.1, except the stabilizer clause: that `B(G)` is a building in the sense of
  Definition 1.5.5 with a polysimplicial `G(k)`-action, and that a central isogeny `G → G′`
  induces an isomorphism `B(G) → B(G′)`. The second part concerns the construction `G ↦ B(G)`.
- Axiom 4.1.4 (A 2), on the maps `A(S) → A(gSg⁻¹)`. In these data the other apartments are the
  translates `g · A(S)` (module `ValuationBuildingAxioms`).
- Axiom 4.1.9: that `(G(k)^0_C, N(k) ∩ G(k)^0)` is a Tits system in `G(k)^0` whose building is
  `B(G)`. The Library has `Langlands.Group.IsTitsSystem`, but no building of a Tits system to
  compare `B(G)` with.
- Axiom 4.1.16 (the Iwahori decomposition, with the unipotent radicals `U^±`), Axiom 4.1.17
  (compatibility with isomorphisms of pairs `(k, G)`, which concerns the construction), Axiom
  4.1.20 (Bruhat–Tits group schemes) and Axiom 4.1.22 (their reductive quotients). The last two
  need smooth affine `o`-models of `G`.
- The equality of `P.zeroFixer Ω` and `P.parahoric Ω` (KP Propositions 7.6.4 and 7.7.5).
- The uniqueness in Proposition 2.11.17 (part of the published, unproved
  `RootRankOneFactorizationStatement`, not used here), the identity `ψ^u_a = −ψ^{u′}_{−a} = −ψ^{u″}_{−a}` of
  Remark 4.1.7 (as corrected on PDF p. 27), and the existence of smallest affine roots
  (Remark 6.3.17, Proposition 6.3.7).
- The existence of data satisfying any of these conditions.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Printed page numbers are
  the PDF page numbers minus 31.
  - Proposition 2.11.17 (book PDF p. 167, printed p. 136);
  - Axioms 4.1.1 and 4.1.2 (book PDF pp. 188–189, printed pp. 157–158);
  - Axiom 4.1.4 (book PDF pp. 189–190, printed pp. 158–159);
  - Axiom 4.1.6, Remark 4.1.7, the definition of `G(k)^0_Ω` and Axiom 4.1.8 (book PDF
    pp. 190–191, printed pp. 159–160);
  - Definition 4.1.26 (book PDF p. 196, printed p. 165);
  - Definition 6.1.2 and the translation action before Lemma 6.1.6 (book PDF pp. 230–231, printed
    pp. 199–200);
  - §6.2, the hyperplanes `H_u` and Proposition 6.2.1 (book PDF p. 243, printed p. 212);
  - Definitions 6.3.1 and 6.3.4 (book PDF pp. 248–249, printed pp. 217–218);
  - Proposition 6.3.13 and Remarks 6.3.16–6.3.17 (book PDF pp. 252–253, printed pp. 221–222);
  - Definition 7.4.1 (book PDF p. 286, printed p. 255);
  - Proposition 7.6.4 (book PDF p. 296, printed p. 265).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  - PDF p. 27: `∪ {1}` in AS 3; the sign in the last line of Remark 4.1.7; "In Axiom 4.1.8(2), it
    should be emphasized that `Ω` is assumed non-empty and bounded"; the corrected axiom list of
    Definition 4.1.26.
