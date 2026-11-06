# A positive-exponent constituent of a reducible maximal-Levi induction

Author: Worker 1714. Module `Langlands.Representation.Exponents.MaximalLeviSupercuspidalPositiveConstituentStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module contains one `Prop`-valued definition, `MaximalLeviSupercuspidalPositiveConstituentStatement`. It is neither assumed nor proved here.

## Statement

The binders and hypotheses are those of the published `MaximalLeviSupercuspidalUnitarizableConstituentStatement` (statement C of module `MaximalLeviReducibilityUnitaryInputs`), word for word:

- a nonarchimedean local field `k` (`Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`, `T2Space`);
- a connected reductive group scheme `G` over `Spec k`, whose rational points carry `RationalPointFamily.pointTopology` and are assumed locally compact and a nonarchimedean group;
- actual rational parabolic data `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` with `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`, `LeviSubgroup.IsGeometricUnipotentRadical r` and `IsIso (subgroupMultiplication l r)`, where `p` is proper (`¬ IsIso p`) and maximal (every parabolic `q : Q ⟶ G` through which `p` factors as `j ≫ q` has `j` or `q` an isomorphism);
- `M(F)` with `leviPointTopology l hl`, and an irreducible `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is supercuspidal (its normalized Jacquet module along every actual non-isomorphism parabolic `p' : P' ⟶ M` is a subsingleton);
- `ρ` has no unitary central character (`IsEmpty (UnitaryCentralCharacter ρ.representation)`);
- `π = (leviInductionFunctor p l r hp hr hl hmul).obj ρ` is not irreducible and has a `UnitaryCentralCharacter`.

The conclusion: there is an irreducible `W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with `HasPositiveRepresentedJacquetExponents W`, together with an injective morphism `W ⟶ π` or a surjective morphism `π ⟶ W`.

`HasPositiveRepresentedJacquetExponents` is the published predicate of `CasselmanSufficiencyAssembly`, the right-hand side of the published `ArbitraryParabolicCasselmanCriterionStatement`: for every actual rational parabolic `p : P ⟶ G` with rational Levi `l`, matching radical `r`, split component `a : A ⟶ M`, compatible `ParabolicRootPresentation p l a` and character `χ` of `A(F)`, if `χ` is a normalized Jacquet exponent of `W` along `(p, l, r)` (`IsNormalizedJacquetExponent`), then its normalized real part lies in the presentation's `positiveCone`.

The only addition to the binder block of statement C is `haveI := hG.smooth`, which supplies the `LocallyOfFiniteType G.X.hom` instance that `HasPositiveRepresentedJacquetExponents` requires. It is an instance derived from the hypothesis `hG`, not a new assumption.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source ID `renard-2026-representations-groupes-reductifs-padiques`: the proof of Théorème VII.1.3 (printed pp.224–226 / PDF pp.230–232).

The proof writes `0 → π_1 → π → π_2 → 0` with `π_1, π_2` irreducible (VI.5.3, VI.5.4, PDF p.179). It distinguishes the cases `|χ(a)| > 1` and `|χ(a)| < 1` on `A_M^{++}` for the central character `χ` of `ρ`; the case `|χ| = 1` is excluded by the hypothesis that `ρ` has no unitary central character. In the third case it concludes that "le critère de Casselman s'applique à la représentation `π_1`, puisque `r_Q^G π_1 = 0` pour tout sous-groupe parabolique standard propre `Q ≠ P`, et que `r_P^G π_1 = ρ`" (PDF p.231): the exponents of `π_1` are those of `ρ`, which satisfy the strict inequality of Casselman's criterion (VII.1.2, PDF p.227). In the second case it passes to the contragredient; equivalently, the exponents of the quotient `π_2` lie in the positive cone. In both cases one constituent, a subrepresentation or a quotient of `π`, has all its exponents in the positive cone.

## Provenance and use

This is a derived statement. It isolates the exponent condition that the proof of VII.1.3 establishes before applying Casselman's criterion. The published statement C replaces it by the consequence of that criterion (unitarizability). The two are linked as follows; a proof module will contain this reduction:

1. `W` inherits the unitary central character of `π` along the injective or surjective morphism.
2. `W` is admissible by the published `RationalPointsIrreducibleAdmissibleStatement` (Renard VI.2.2).
3. The published `ArbitraryParabolicCasselmanCriterionStatement` (VII.1.2) turns the positive exponents into square-integrability modulo the center.
4. That gives unitarizability (IV.3.2), as in the published `rationalSquareIntegrableUnimodularForm`, which uses the ambient unimodularity statement.

Renard's argument proves the statement. A square-integrable irreducible admissible representation with unitary central character satisfies the exponent condition (the necessity direction of VII.1.2), and Renard shows that `π_1` or `π_2` is square-integrable modulo the center.

## Faithfulness notes

- The exponent condition is the Library's all-represented-parabolic condition. It quantifies over every actual rational parabolic of `G`, including non-proper ones, and over every compatible root presentation, not only standard parabolics for one minimal parabolic. This is exactly the condition of the published Casselman criterion, so the statement does not choose standard data.
- Statement C's two cases (subrepresentation or quotient) are kept. The statement does not say which case occurs, and it does not identify `W` with `π_1` or `π_2`.
- Universes are as in statement C: `ρ` in `SmoothRep.{0, u, v}`, `π` and `W` in `SmoothRep.{0, u, max u v}`.
