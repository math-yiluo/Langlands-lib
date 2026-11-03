# Nested semistandard parabolic decomposition target

`DynamicNestedParabolicDecompositionStatement` is a proposition target over
every field `k : Type u` and every connected reductive group scheme `G`
over `Spec k`. For cocharacters `χ, ψ`, it assumes only
`Dynamic.IsCompatibleNestedPair χ ψ`: the all-test inclusions
`P(χ) ≤ P(ψ)` and `Z(χ) ≤ Z(ψ)`, and simultaneous realization of both
cocharacters in one ambient maximal split torus.

Write `P = P(χ)`, `M = Z(χ)`, `N = U(χ)`, `Q = P(ψ)`,
`L = Z(ψ)` and `U = U(ψ)`. The conclusion
`Dynamic.NestedParabolicDecomposition χ ψ` asserts on every test scheme
`X`:

- `L ∩ P = M (L ∩ N)`;
- `N = (N ∩ L) U`;
- `P = (L ∩ P) U`.

These are equalities of actual subsets of `Hom(X,G)`, with pointwise
multiplication. The conclusion also includes the factor containments,
normality of `(L ∩ N)(X)` in `(L ∩ P)(X)` and the complement assertion
expressing uniqueness of that Levi decomposition. In the second formula,
the implementation uses the equal intersection `L ∩ N`. All test schemes,
including nonreduced ones, occur in the quantifier. Applying
`SubgroupFunctor.NestedLeviDecomposition.identityTest_products` gives
the three formulas at the identity test `Spec k → Spec k`, hence the
formulas for actual rational point subgroups.

The hypotheses do not contain a decomposition, a unipotent inclusion, a
parabolic correspondence, an abstract equivalence, splitness of `G`, or a
root-system classification axiom. The common torus and inclusion `M ≤ L`
make the choice of compatible Levis explicit. The target asserts no
existence of compatible data for an unrelated pair of chosen Levis.
Dynamic subgroup functors are already defined; their representability,
parabolicity and centralizer reductivity have separate structural owners.

## Source and derived scope

Renard, 9 July 2026 edition, VI.1.4, printed p.136 (PDF p.142), uses
precisely these three decompositions for nested **semistandard**
parabolics. V.3.10–V.3.11, printed p.112 (PDF p.118), supplies the
intersection and parabolic-in-Levi correspondence. The 2010-edition
corrections, PDF p.9 (printed-p.156 entry), explicitly add the
semistandard hypothesis to VI.1.4. The governing source here is the
corrected 2026 edition, over a nonarchimedean local field.

The arbitrary-field and all-test formulation is **derived** from the
rational parabolic/Levi structure in Borel–Tits §4.4(c) and §4.7,
printed pp.86–88 (PDF pp.33–35), with the cocharacter description in
Milne §25.1 and §25.6–25.7, printed pp.544–546 (PDF pp.560–562).
Borel–Tits §0.3 permits affine absolutely reduced group schemes over
arbitrary fields. The proposition is the corresponding modern dynamic
functor target; these citations do not constitute a Lean proof.

The official Milne Chapter 25 errata was checked: the corrected
§25.6(b) concerns minimal parabolics. This target does not identify an
arbitrary Levi with the centralizer of a maximal split torus by that
clause. It also does not assume the classical relative-root-system proof,
whose incompleteness the errata records.

The conditional standard-index bridge is developed separately in
`DynamicNestedParabolicDecompositionReduction`. It transports realizing
standard cocharacters through the published
`StandardCocharacterStatement` and `StandardParabolicOrderStatement`
targets. In particular it retains all-test products for
`standardParabolic`, `standardLevi` and `standardUnipotent`, and recovers
`StandardLeviIntersectionStatement`. Those structural targets are
hypotheses of that bridge, not hypotheses of this final target.
The existing standard-index proof task
`1d7d4767-a668-4ce1-9989-319a625f6de3` remains an independent obligation.

This module defines a `Prop`; it provides no proof, instance or axiom
asserting it. Its exact proof remains a separate successor task.

Source IDs:
`renard-2026-representations-groupes-reductifs-padiques`,
`renard-2010-corrections-complements`,
`borel-tits-1965-groupes-reductifs`,
`milne-2017-algebraic-groups`,
`milne-2017-algebraic-groups-errata-2026-11-02`.
