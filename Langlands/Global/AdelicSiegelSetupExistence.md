# Existence of the actual algebraic Siegel setup from three structural statements

Author: Worker 4149 (formerly Worker 0).

This module isolates the algebraic half of the Library target
`Langlands.Global.AdelicSiegelFactors.AdelicGoodSiegelReductionStatement`. It states
that the actual algebraic setup `IsSiegelAlgebraicSetup` exists for every connected
reductive group over a number field, and it proves this statement from three published
structural propositions that are not yet proved. Every other clause of the setup comes
from published proofs. The module proves no analytic assertion: no compact subgroup,
Iwasawa decomposition or Siegel coverage is constructed or assumed.

## The statement

`AdelicSiegelFactors.SiegelAlgebraicSetupExistenceStatement` is a definition returning
`Prop`, in universe `u`. It quantifies over every number field `F : Type u` and every
group scheme `G` over `Spec F` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`, and assumes `IsConnectedReductive G`. It asserts that there
are commutative group schemes `T` and `T₀` over `Spec F`, a map `i : T.toGrp ⟶ G`, a
cocharacter `ν : cocharacterLattice T` and a map `j : T₀ ⟶ T` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`.

The binders and instance arguments are exactly those of `AdelicSiegelReductionStatement`
and `AdelicGoodSiegelReductionStatement`, and the conclusion is exactly the first
existential block of both. `IsSiegelAlgebraicSetup` is used unchanged; see
`AdelicSiegelReductionStatement.md` for its nine clauses: maximal split torus, generic
cocharacter, minimality of the canonical standard parabolic, rational Levi, geometric
unipotent radical, Levi equal to the torus centralizer, positive roots equal to the
roots on `Lie P`, a derived subgroup with a maximal split torus `T₀` mapping through `j`,
and a split component `Z₀ → T` with scheme-surjective multiplication `T₀ × Z₀ → T`.

*Provenance (derived).* The statement is the setup-existence part of the published
`AdelicSiegelReductionStatement`, whose Markdown compares the setup with Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §2.7, the setup preceding
(2.25). That passage, printed p.71 (PDF p.88), reads: "Assume that `P` is a minimal
parabolic subgroup of `G` with unipotent radical `N`. Fix a Levi subgroup `M ≤ P`. Let
`T₀` be a maximal split torus of `G^der` contained in `M` and let `Z₀` be the maximal split
torus of `Z_G`. Then `T := T₀Z₀` is a maximal split torus of `G`. As mentioned in §1.9,
the set of nonzero weights of `T` acting on `Lie P` is a set of positive roots with respect
to a unique base `Δ ⊂ Φ(G, T)`." The nine clauses above record this data for the
canonical standard representatives. No new mathematical object or convention is
introduced. Splitting it off lets
consumers of the algebraic setup, such as finite-volume arguments, depend on it without
the analytic coverage.

## The structural inputs

The conditional theorem takes three published Library propositions as hypotheses, all
in the same universe `u`:

- `Langlands.GroupScheme.GenericMinimalParabolicStatement`
  (`GroupScheme.Rational.MinimalParabolicStatement`): for a maximal split torus `i` of a
  connected reductive group over a field and a generic cocharacter `ν`, the dynamic
  parabolic `Dynamic.parabolic (ν ≫ i)` is a minimal parabolic subgroup functor. Its proof
  task is `bc8072c0-8a2b-4636-ab3c-7f04a4afb6a5`.
- `Langlands.GroupScheme.DerivedMaximalSplitTorusStatement`
  (`GroupScheme.Derived.MaximalSplitTorusStatement`): for a derived subgroup `d : D ⟶ G`
  and a maximal split torus `i : S ⟶ G`, some maximal split torus `j : S_D ⟶ D` and closed
  `e : S_D ⟶ S` satisfy `j ≫ d = e ≫ i`. Its proof task is
  `45bba50f-b29d-49c2-b923-64037208e2e1`.
- `Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement`
  (`GroupScheme.Derived.CentralSplitTorusProductStatement`): for such compatible data and
  a split component `a : A ⟶ G` factoring as `c ≫ i`, the multiplication
  `prodHom e c : S_D × A ⟶ S` is a central isogeny. Its proof task is
  `52f33732-d993-43ae-aa80-b0bd915c3034`.

## Declarations and proofs

**`Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal`** (namespace
`Langlands.GroupScheme`). For a field `k`, a group scheme `G` over `Spec k` with
`IsAffineHom G.X.hom`, `i : T.toGrp ⟶ G` and `ν`, it assumes
`GenericMinimalParabolicStatement`, `IsConnectedReductive G`, `IsMaximalSplitTorus i` and
`IsGenericCocharacter i ν`, and concludes
`IsMinimalParabolicSubgroup (Standard.parabolicHom i ν ∅)`.
*Proof.* The statement gives `IsMinimalParabolicFunctor (Dynamic.parabolic (ν ≫ i))`. The
published `standardParabolic_empty_eq_dynamic_of_generic` rewrites the dynamic parabolic
as `standardParabolic i ν ∅`, and representability
(`Standard.isRepresentedBy_parabolicHom`) rewrites that as
`SubgroupFunctor.range (Standard.parabolicHom i ν ∅)`. By
`isMinimalParabolicFunctor_iff_exists` some actual minimal parabolic `j'` has the same
range. `IsParabolicSubgroup.of_range_eq` transfers parabolicity to the closed subgroup
`Standard.parabolicHom i ν ∅` (`Standard.isClosedSubgroup_parabolicHom`), and minimality
transfers because the two ranges are equal.

**`AdelicSiegelFactors.subgroupProductMap_eq_prodHom`.** For commutative group schemes
`A`, `B`, `C` over any scheme and maps `a : A ⟶ C`, `b : B ⟶ C`, the scheme map
`subgroupProductMap (groupHom a) (groupHom b)` used in the setup equals the underlying
map of the published product homomorphism `prodHom (groupHom a) (groupHom b) _`.
*Proof.* Evaluate the published formula `comp_prodHom` at the identity point of
`A.X ⊗ B.X`; its two coordinates are the projections.

**`AdelicSiegelFactors.siegelAlgebraicSetupExistence_of_structural`** proves
`SiegelAlgebraicSetupExistenceStatement` from the three structural statements.
*Proof.* Fix `F`, `G` and `hG`.

1. `cocharacterMaximalSplitTorus`, applied to the trivial cocharacter, gives a maximal
   split torus `i : T ⟶ G`. `IsSplitTorus.exists_genericCocharacter` gives a generic
   cocharacter `ν` of `i`.
2. `derivedSubgroupRepresentability` gives `d : D ⟶ G` with `IsDerivedSubgroup d`. The
   derived maximal split torus statement gives `t₀ : T₀ ⟶ D` maximal split and closed
   `e : T₀ ⟶ T` with `t₀ ≫ d = e ≫ i`. Take `j = e`.
3. `splitComponentStatement` gives a split component `a : A ⟶ G`, and
   `IsSplitComponent.exists_commFactor_of_isMaximalSplitTorus` gives `c : A ⟶ T` with
   `c ≫ i = a`. Take `Z₀ = A` and `z = c`.
4. The clauses are then supplied as follows. Maximality and genericity come from step 1.
   Minimality comes from the lemma above. The rational Levi and geometric unipotent
   radical clauses come from `standardMinimalLeviStructure`. The Levi equals the torus
   centralizer by `standardLevi_empty_eq_torusCentralizer_of_generic`. The roots on
   `Lie P` are the positive roots by `relativeRoots_torusToStandardParabolic`. The derived
   clause is step 2 with witnesses `D`, `d`, `t₀`. The split component clause is
   `c ≫ i = a` together with `IsSplitComponent a`. Surjectivity of the multiplication
   `T₀ × A ⟶ T` follows from the central isogeny of the product statement
   (`IsCentralIsogeny.surjective`) after `subgroupProductMap_eq_prodHom` identifies the two
   scheme maps.

The universe, the number field and the group are arbitrary. Nonsplit and anisotropic
groups are included: then `T` and `T₀` may have rank zero and the root sets are empty.
The theorem adds no hypothesis beyond the three named statements.

## What remains

The three structural statements are unproved; once their proof tasks publish proofs,
applying `siegelAlgebraicSetupExistence_of_structural` to them proves
`SiegelAlgebraicSetupExistenceStatement`. The compact subgroup with Iwasawa decomposition
and positive-torus compatibility, and the Siegel coverage itself, are separate obligations
of task `6adbbc46-4bb2-4c01-843a-d8ded48189f2`.
