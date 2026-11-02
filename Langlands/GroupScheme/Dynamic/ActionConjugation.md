# Cocharacter conjugation and abstract dynamic functors

This module compares the abstract automorphic action construction with the
published cocharacter dynamic construction on actual group schemes. Its base
`S` is an arbitrary scheme and every statement uses all `T : Over S`.

## Sources and provenance

Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §2.1
introduction, printed p.45 / PDF p.71, and Remark 2.1.11, printed p.59 / PDF p.85,
identify conjugation along a one-parameter subgroup as a special case of an
abstract left action by group automorphisms. The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.11(a),
printed pp.130–132 / PDF pp.161–163, uses extension of the orbit map from
`Gm` to the affine line and its value at zero, and explicitly permits an
abstract action. The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections, version of 1 November 2024, PDF pp.24–26,
registered as `kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
correct notation in Proposition 2.11.1 without changing these definitions.

The sources phrase these definitions over affine bases, using algebra points.
The Library's two constructions extend the elementary definitions intrinsically
to arbitrary base and test schemes: one action morphism induces the point
actions, orbit maps are morphisms on the actual products, and the invariant
condition tests every refinement. This module proves their equality in the
conjugation case. It introduces no additional geometric hypothesis and proves
no general representability or structure theorem. In particular, it does not
identify invariants with an intersection of opposite parabolics for an
arbitrary nonaffine group.

The comparison declarations and the restriction identity are derived interface
results. Their proofs use the published normalized-conjugation formulas,
`Dynamic.Basic`, `Rational.TorusCentralizer`, and the abstract `Dynamic.Action`.

## Restriction of the action

Declarations lie in `Langlands.GroupScheme.AutomorphicAction`.

`ext_act` proves that equality of induced point actions implies equality of the
actions: evaluate at the universal pair of projections from `H ×_S G` to
recover the underlying action morphism, then use proof irrelevance for its
laws.

For actual homomorphisms `f : K ⟶ H` and `i : H ⟶ G`,
`restrict_conjugation` proves that restricting `conjugation i` along `f` equals
`conjugation (f ≫ i)`. The proof evaluates both actions on all test points,
uses the existing conjugation point formula, and composes the homomorphisms.

For a cocharacter `χ : (Gm S).toGrp ⟶ G`, `cocharacterAction χ` is explicitly
`(conjugation (𝟙 G)).restrict χ`. Thus its input is the actual homomorphism
into the ambient group. `cocharacterAction_eq_conjugation` identifies it with
`conjugation χ`, and `cocharacterAction_act` proves the formula
`χ(t) * g * χ(t)⁻¹` on every test scheme.

## Orbit, extension and limit comparisons

`cocharacterAction_orbit` proves equality of the actual orbit morphisms with
`Dynamic.orbit χ`. It applies the point formula on `T ×_S Gm` at the universal
`Gm` point and the pullback of `g`.

`cocharacterAction_isOrbitExtension` proves equivalence of the abstract and
published extension predicates for the same `g` and the same morphism
`e : T ×_S AffineLine.scheme S ⟶ G.X`. Both restrict along precisely the
published `AffineLine.unitInclusion S`, so rewriting the orbit equality
proves the result.

`cocharacterAction_hasLimit` proves equivalence with `Dynamic.HasLimit χ g l`
for every specified `l`. Both constructions use `Dynamic.evalZero` itself,
with the same zero section. The proof rewrites the extension predicate under
the existential quantifier; it chooses no unique extension or limit.

## Subgroup functor comparisons

`cocharacterAction_parabolic`, `cocharacterAction_centralizer`, and
`cocharacterAction_unipotent` prove equality with `Dynamic.parabolic χ`,
`Dynamic.centralizer χ`, and `Dynamic.unipotent χ`, respectively.

For the parabolic and unipotent functors, subgroup-functor extensionality reduces
to each test scheme, and the extension or limit comparison identifies membership.
For the centralizer, the abstract functor is the all-refinement invariant
subgroup. The proof first identifies the restricted action with conjugation
along `χ`, then reuses
`conjugation_fixedSubgroup_eq_torusCentralizer` and
`torusCentralizer_gm_eq_dynamicCentralizer`. This retains the universal,
scheme-theoretic invariance condition rather than testing only `Gm(T)`.

No separatedness, smoothness, affineness, finite presentation, or reducedness
assumption is used. The module constructs neither a semidirect product group
scheme nor quotient-action descent or relative root groups.
