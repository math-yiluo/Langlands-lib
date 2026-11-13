# Renard VI.10.8 from VI.6.3, VI.7.4 and VI.10.7 (conditional reduction)

Source: D. Renard, *Représentations des groupes réductifs p-adiques* (French
version, 2026), VI.10.8 "Retour sur le théorème de Howe", Théorème and its
proof, printed p.217 / PDF p.223.

## The reduction statement

`Langlands.Aubert.General.RepresentedParabolic.CenterFiniteHoweReductionStatement.{u, v}`
is the implication

```
RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v} →
FiniteTypeCenterAdmissibleStatement.{u, v} →
FiniteTypeComponentCharacterizationStatement.{u, v} →
BernsteinCentralIdempotentStatement.{u, max u v} →
CenterFiniteHoweStatement.{u, v}
```

All five are published statements, used unchanged. This is an internal reduction
statement, not a statement printed by Renard. The theorem
`centerFiniteHoweReduction` proves it, as `centerFiniteHowe_of_inputs`.

## What is proved

`Langlands.Aubert.General.RepresentedParabolic.centerFiniteHowe_of_inputs`
proves the published target `CenterFiniteHoweStatement.{u, v}` from four
published statements, which are **explicit unproved hypotheses**:

| Hypothesis | Renard | Universe |
| --- | --- | --- |
| `SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | VI.6.3 (Howe) | `.{u, v}` |
| `FiniteTypeCenterAdmissibleStatement` | VI.10.7, Théorème | `.{u, v}` |
| `CuspidalSupport.FiniteTypeComponentCharacterizationStatement` | VI.10.7, Lemme and Proposition | `.{u, v}` |
| `CuspidalSupport.BernsteinCentralIdempotentStatement` | VI.7.4, first paragraph | `.{u, max u v}` |

So this file is a conditional reduction. It does **not** prove
`CenterFiniteHoweStatement`. That still needs proofs of the four hypotheses,
which are owned by other tasks. Once those proofs are published, the target
follows by applying `centerFiniteHowe_of_inputs` to them.

The remaining declarations carry no hypotheses:

- `SmoothRep.orthogonal_of_pointwise_complete`: let `p i` be commuting
  idempotent linear endomorphisms of a vector space over a field of
  characteristic zero. Suppose only finitely many `p i x` are nonzero for each
  `x`, and `∑ᶠ i, p i x = x`. Then `p s * p t = 0` for `s ≠ t`.
- `SmoothRep.catCenterUniverseRestrict`, `SmoothRep.hom_app_universeLift`: a
  central transformation of the lifted category `SmoothRep.{0, uG, max uV uX}`
  restricts along the fully faithful carrier lift `universeLiftFunctor` to one of
  `SmoothRep.{0, uG, uV}`, and acts on `universeLift A` through that restriction.
- `SmoothRep.finiteDimensional_centerOperatorSpan_universeLift`: if the span of
  the centre operators on `A` is finite-dimensional, so is the span on
  `universeLift A`. Every operator on the lift is the conjugate of a centre
  operator on `A` by the carrier equivalence.
- `SmoothRep.centerOperator_mul`: `z ↦ (z.app A)` is multiplicative from
  `CatCenter` to `Module.End ℂ A`.
- `SmoothRep.centerOperator_orthogonal`: central idempotents that sum to the
  identity, pointwise finitely, act on each object by pairwise orthogonal
  projections. This combines the two previous facts with the commutativity of
  `CatCenter`.

## The proof

Write (1) finite type (`Module.Finite` over `MonoidAlgebra ℂ G(F)`), (2)
admissible, (3) `ℨ(G)`-finite (the centre operators on `π` span a
finite-dimensional space, `centerOperatorSpan π`).

**(1) and (2).** `finite_centerOperatorSpan_of_finiteType_admissible` (already
in the Library) gives (3), and Howe's hypothesis gives finite length. Renard
derives (3) from finite length by induction on the length and Schur's lemma. The
Lean proof uses instead the published direct argument: evaluate the centre on
finitely many generators fixed by one compact open subgroup.

**(1) and (3).** This is Renard's argument. The VI.10.7 Theorem hypothesis
makes `π` `ℨ(G)`-admissible. Then `isAdmissible_of_centerAdmissible_centerFinite`
makes every `V^K` finite-dimensional, so `π` is admissible. Howe then gives
finite length.

**(2) and (3).** This is `finiteType_of_admissible_centerFinite`, which follows
Renard's argument with these choices:

1. A standard family is constructed with no extra premise: a maximal split torus
   and generic cocharacter from `exists_maximalSplitTorus_genericCocharacter`,
   and the family from `Jacquet.standardBernsteinFamily`. `LocallyOfFiniteType`
   follows from smoothness of `G`.
2. The argument runs on `L = universeLift.{u} π`, with carrier in
   `Type (max u v)`. This is the carrier of the published Proposition and of the
   inertial supports. `L` is admissible (`isAdmissible_universeLift_iff`). It is
   `ℨ(G)`-finite for the centre of the lifted category
   (`finiteDimensional_centerOperatorSpan_universeLift`).
3. The VI.7.4 hypothesis at `.{u, max u v}` gives central idempotents `e_𝔰` on
   the carrier `max u v`. Each `e_𝔰` is the identity on the block `M(G)_𝔰`, and
   on each vector only finitely many `e_𝔰` are nonzero, with sum the identity.
   By `centerOperator_orthogonal` they act on `L` by pairwise orthogonal
   projections. By the published `finite_centralOperatorSupport`, only finitely
   many `e_𝔰` act nontrivially on `L`. This is the finite-dimensional version
   of Renard's "an ideal of finite codimension contains `ℨ_𝔰` for all but
   finitely many `𝔰`".
4. Let `σ` be a subquotient of `L` with inertial support `𝔰`. Then `σ` is
   irreducible. By `NormalHecke.nonempty_iso_of_isSubquotient`, each of its
   irreducible subquotients is isomorphic to it, so `σ` satisfies the saturated
   block property and hence (`bernsteinBlockProperty_iff_saturated`)
   `bernsteinBlockProperty 𝔰 σ`. So `e_𝔰` acts on `σ` as the identity. By
   `mem_centralOperatorSupport_of_subquotient`, `e_𝔰` then acts nontrivially
   on `L`. This is Renard's "the identity of `ℨ_𝔰` acts by the identity on
   `V_𝔰`". So the set of inertial supports of subquotients of `L` is finite.
5. `L` is `ℨ(G)`-admissible (`IsAdmissible.isCenterAdmissible`). The backward
   direction of the Proposition hypothesis then makes `L` of finite type, and
   `moduleFinite_universeLift_iff` brings this down to `π`. Howe gives finite
   length.

Axioms: only `propext`, `Classical.choice` and `Quot.sound` (checked by
inspecting `centerFiniteHowe_of_inputs`).
