# Exponents along the parabolics with Levi factor `M` in Renard VII.1.3

Author: Worker 1714. Module `Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviExponentStatements`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module contains one predicate, `HasPositiveLeviJacquetExponents`, and two `Prop`-valued statements:

- `MaximalLeviSupercuspidalExponentTransferStatement` (the transfer step);
- `MaximalLeviSupercuspidalLeviPositiveConstituentStatement` (the constituent step).

Neither statement is assumed or proved here. Together they split the exponent part of the proof of Renard VII.1.3. The published statement `MaximalLeviSupercuspidalPositiveConstituentStatement` (module `MaximalLeviSupercuspidalPositiveConstituentStatement`) records that part. The module imports `MaximalLeviReducibilityUnitaryInputs` (for `leviInductionFunctor`, `jacquetFunctor`, `UnitaryCentralCharacter` and the Levi-point instances) and `CasselmanSufficiencyAssembly` (for `HasPositiveRepresentedJacquetExponents`).

## The predicate `HasPositiveLeviJacquetExponents`

`HasPositiveLeviJacquetExponents (m : M ⟶ G) π` is the published `HasPositiveRepresentedJacquetExponents π`, restricted to some of the parabolics. It ranges over the actual rational parabolics `q : Q ⟶ G` (`IsParabolicSubgroup q`) whose rational Levi `lQ : M ⟶ Q` (`IsRationalLeviSubgroup lQ`) has the fixed group scheme `M` as its source and satisfies `lQ ≫ q = m`. The data that the published predicate takes are unchanged:

- a geometric unipotent radical `rQ : U ⟶ Q` with `IsIso (subgroupMultiplication lQ rQ)`;
- a split component `a : A ⟶ M` (`IsSplitComponent a`);
- a compatible `ParabolicRootPresentation q lQ a`;
- a character `χ` of `A(F)` that is a normalized Jacquet exponent of `π` along `(q, lQ, rQ)` (`IsNormalizedJacquetExponent`).

For each such `χ`, the predicate asks that its normalized real part lies in the presentation's `positiveCone`.

The two statements use it with `m = l ≫ p`, the Levi subgroup `M` of the given parabolic `P` inside `G`. So it constrains the exponents along the parabolics of `G` that have the subgroup `M` as a Levi factor. When `P` is a maximal proper parabolic, these are `P` and its opposite parabolic `P̄`, up to isomorphism of the parabolic. Renard's proof computes the exponents of `π₁` and `π₂` along exactly these parabolics, as `r_P` and `r_{P̄}` (the latter through `r_{P'}` and the element `w`).

The predicate is a definition, not a hypothesis. Its variables (`k`, `G`, `M` and the instances on `rationalPoints G`) are section variables, matching those of `HasPositiveRepresentedJacquetExponents`.

## The transfer statement

`MaximalLeviSupercuspidalExponentTransferStatement` has the following binder block:

- a nonarchimedean local field `k` and a connected reductive `G`;
- the actual maximal proper rational parabolic data `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`;
- the instances on `M(F)`;
- an irreducible supercuspidal `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)`.

These are taken word for word from the published `MaximalLeviSupercuspidalUnitarizableConstituentStatement` (statement C), with `haveI := hG.smooth` added as in `MaximalLeviSupercuspidalPositiveConstituentStatement`. It assumes that `π = (leviInductionFunctor p l r hp hr hl hmul).obj ρ` has a `UnitaryCentralCharacter`. Unlike statement C, it does not assume that `ρ` has no unitary central character or that `π` is reducible.

The conclusion concerns every `W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with an injective morphism `W ⟶ π` or a surjective morphism `π ⟶ W`. Such a `W` need not be irreducible. If `HasPositiveLeviJacquetExponents (l ≫ p) W` holds, then `HasPositiveRepresentedJacquetExponents W` holds: the exponent condition then holds along every actual rational parabolic of `G`.

This is the reasoning in Renard's sentence "le critère de Casselman s'applique à la représentation `π₁`, puisque `r_Q^G π₁ = 0` pour tout sous-groupe parabolique standard propre `Q ≠ P`" (PDF p.231). Renard checks only standard parabolics, using his Remark VII.2.1.3 that every parabolic is conjugate to a standard one. The Library's condition ranges over all actual parabolics. The intended proof of the transfer statement is the following:

1. The exponents of `W` along any parabolic `Q = LU_Q` are exponents of `π` (exactness of the Jacquet functor).
2. By the geometric lemma (VI.5.3), each exponent of `π` along `Q` comes from a piece attached to a double coset. Supercuspidality of `ρ` kills every piece except those with `L ⊇ zMz⁻¹`.
3. If `Q` is proper, then `L = zMz⁻¹` because `M` is a maximal Levi subgroup. Conjugating by `z` turns `Q` into a parabolic with Levi factor `M` and transports exponents and cones, so the hypothesis applies.
4. If `Q = G`, the exponents are the restrictions of the central character of `W` to the split center. They have real part `0` because `π`, and hence `W`, has a unitary central character. The cone of the trivial parabolic is `{0}`.

The proof uses neither hypothesis that it drops. Dropping them makes it a statement about all subrepresentations and quotients of `i_P^G ρ`.

## The constituent statement

`MaximalLeviSupercuspidalLeviPositiveConstituentStatement` has exactly the binders and hypotheses of statement C, with `haveI := hG.smooth` added:

- `ρ` irreducible and supercuspidal, with no unitary central character;
- `π` not irreducible, with a unitary central character.

Its conclusion: there is an irreducible `W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` satisfying `HasPositiveLeviJacquetExponents (l ≫ p) W`, together with an injective morphism `W ⟶ π` or a surjective morphism `π ⟶ W`.

This is Renard's choice between `π₁` and `π₂` in the exact sequence `0 → π₁ → π → π₂ → 0` (VII.1.3.2, PDF p.231). Let `χ` be the central character of `ρ`. The case `|χ| = 1` on `A_M` is excluded by the hypothesis on `ρ`.

- **Case `M ≠ M'`.** `r_P π₁ = ρ`, `r_{P'} π₁ = 0`, `r_P π₂ = 0` and `r_{P'} π₂ = ρ'`. Among the parabolics with Levi factor `M`, `π₁` has exponents only along `P`, where they are those of `ρ`. The quotient `π₂` has exponents only along `P̄` (Renard: `r_{P̄}` is `r_{P'}` composed with `w`), where they are given by `χ` through `w`.
- **Case `M = M'`.** `r_P π₁ = ρ`, `r_P π₂ = ρ' = ρ^w`, and `w·P = P̄`. Since `w` acts by `−1` on `a_M/a_G` and the cone of `P̄` is the negative of that of `P`, the exponents along `P̄` are again governed by `±Re χ`. If `ρ ≅ ρ^w`, then `Re χ` vanishes on `a_M/a_G`. Together with the unitary central character of `π`, this would make the central character of `ρ` unitary, so this case cannot occur.

In each case, `π₁` (when `|χ| < 1` on `A_M^{++}`) or `π₂` (when `|χ| > 1`) has all its exponents along `P` and `P̄` in the positive cones. Renard treats the second case through the contragredient. Here the quotient `π₂` is used directly, which is the equivalent dual formulation.

## Use

The published `MaximalLeviSupercuspidalPositiveConstituentStatement` follows from the two statements:

1. The constituent statement gives an irreducible sub or quotient `W` of `π` with `HasPositiveLeviJacquetExponents (l ≫ p) W`.
2. The hypotheses of the transfer statement are a subset of those of the constituent statement, so the transfer statement upgrades this to `HasPositiveRepresentedJacquetExponents W`.

The reduction theorem will be in a separate module.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source ID `renard-2026-representations-groupes-reductifs-padiques`. The relevant passages are:

- the proof of Théorème VII.1.3 (printed pp.224–226 / PDF pp.230–232);
- Casselman's criterion VII.1.2 (PDF p.227);
- Remark VII.2.1.3 on conjugacy to standard parabolics (PDF p.233).

## Provenance and faithfulness notes

Both statements are derived. Renard does not state them separately. They record the two halves of the exponent argument that his proof makes before applying Casselman's criterion. The provenance of their hypotheses is as follows:

- The binder blocks are copied from statement C. The only addition is the instance `haveI := hG.smooth`, which `HasPositiveRepresentedJacquetExponents` and `HasPositiveLeviJacquetExponents` require. It is derived from `hG`, not a new assumption.
- The transfer statement omits two hypotheses of statement C: that `ρ` has no unitary central character, and that `π` is reducible. It therefore says more than is needed for statement C.
- Neither statement says which of `π₁` and `π₂` is `W`, and neither names the opposite parabolic or the Weyl element `w`.
- The Levi-restricted condition quantifies over all actual parabolics with Levi `M` (in the sense `lQ ≫ q = l ≫ p`) and over all split components and compatible root presentations. It therefore involves no choice of standard data.
- Universes are as in statement C: `ρ` in `SmoothRep.{0, u, v}`, `π` and `W` in `SmoothRep.{0, u, max u v}`.
