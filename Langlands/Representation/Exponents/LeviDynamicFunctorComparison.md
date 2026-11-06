# Actual represented Levi induction under an exact dynamic presentation

This is an internal comparison of the published represented-parabolic and
dynamic functors. It retains an exact dynamic presentation as input.
It neither constructs that presentation nor proves any of the four
finite-length or cuspidal-support propositions of the host task.

## Data and topology

Let `k : Type u` be a Hausdorff topological field. Let `G`, `P`, `M` and
`U` be group schemes over `Spec k`, with affine structure morphisms for
`G` and `M`. Rational points carry `RationalPointFamily.pointTopology`.
For the Levi this is definitionally the canonical `leviPointTopology l hl`;
the affine instance supplied by `hl` is proof-irrelevant.

The represented data are a parabolic inclusion `p : P ⟶ G`, a rational
Levi `l : M ⟶ P`, its geometric unipotent radical `r : U ⟶ P`, and an
isomorphism `subgroupMultiplication l r`. The comparison additionally
uses a cocharacter `χ` and three identities of subgroup functors:

- `range p = Dynamic.parabolic χ`;
- `range (l ≫ p) = Dynamic.centralizer χ`;
- `range (r ≫ p) = Dynamic.unipotent χ`.

These identities are supplied on all test schemes. The constructions
evaluate them at the identity test object over `Spec k`.

## Point equivalence and closedness

`dynamicLeviPointsEquiv` composes the published `leviPointsEquiv` with
the topological group equivalence induced by equality of the literal
Levi image and the dynamic centralizer's rational-point subgroup.
Its source is the actual group `M(k)`. The theorem
`dynamicLeviPointsEquiv_apply_coe` identifies its ambient value with
`rationalPoints.map (l ≫ p) m`.

`dynamicRadicalClosed` rewrites the dynamic radical's point subgroup
using the supplied radical identity, then applies the published
closed-image theorem to `r ≫ p`. This uses the original radical's
closed immersion and the parabolic's closed immersion.

## Natural comparison of induction

Assume additionally that `G(k)` is locally compact and nonarchimedean.
For an independent representation-carrier universe `v`,
`leviDynamicInductionIso` is a natural isomorphism from
`leviInductionFunctor p l r hp hr hl hmul` to the composite of:

1. coefficient pullback along the inverse of `dynamicLeviPointsEquiv`;
2. `normalizedInductionFunctor` for the published dynamic semidirect
   decomposition and `dynamicRadicalClosed`.

Both functors have domain smooth complex representations of the actual
`M(k)` with carriers in `Type v`, and codomain smooth complex
representations of `G(k)` with carriers in `Type (max u v)`.
The Haar half-modulus normalization is the one already used by the
published normalized induction.

The implemented proof first establishes private identity and composition
isomorphisms for coefficient pullback, with identity linear maps as
components. A private equal-subgroup induction comparison is proved by
substituting the three subgroup equalities. The main proof applies this
comparison to the identity-test evaluations of the supplied presentation,
whiskers by the original inverse Levi-point pullback, explicitly
reassociates the functors, and combines the two coefficient pullbacks.

## Provenance and remaining obligations

All mathematical inputs are imported Library constructions:
`ArbitraryParabolicLeviPoints` supplies the actual Levi-point equivalence,
canonical topology and represented induction;
`DynamicParabolic` supplies the dynamic semidirect decomposition.
The new construction is their transport under supplied exact subgroup
identities, so no new literature assertion is introduced.

Existence of a presenting cocharacter, nested-parabolic realization,
induction in stages, cuspidal embeddings, and the unconditional
finite-length and cuspidal-support results remain separate obligations.
