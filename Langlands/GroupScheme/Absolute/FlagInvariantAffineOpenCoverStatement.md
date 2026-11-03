# Invariant affine neighbourhoods in an actual Borel quotient

This module states the proposition target
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement.{u}`. It does
not prove the existence of the neighbourhoods or the flag step.

Let `k : Type u` be algebraically closed, let `G` be smooth, connected and
affine over `Spec k`, and let `t : T.toGrp ⟶ G` be a maximal torus. Let
`i : U ⟶ G` be a smooth connected unipotent closed subgroup. Assume that
`range i ≤ range b'` for every Borel subgroup `b'` whose range contains
`range t`. These are precisely the group hypotheses of
`UnipotentTorusBorelsToAllBorelsStatement`. In particular, `G` need not be
reductive, and there is no premise that `T` normalizes `U`.

The statement takes any Borel subgroup `b : B ⟶ G` and a supplied actual
scheme quotient `q : G.X ⟶ Q`. The structure morphism `Q.hom` is separated,
locally of finite type and quasi-compact. The projection `q.left` is flat,
surjective and quasi-compact. Its right-coset fibers are specified on every
scheme test `Z`:

```text
g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Z.
```

It also takes an actual `SchemeAction G Q` satisfying the usual quotient
action law on all lifted cosets. These hypotheses specify the homogeneous
quotient and its action, rather than assuming an arbitrary projective
scheme or an arbitrary action. The published
`Dynamic.flagQuotientSchemeAction` constructs such an action from the
flat, surjective, quasi-compact quotient and its fiber law; its
`flagQuotientSchemeAction_act_lift` is the required action law. The smooth
quotient projections supplied by
`SmoothSubgroupQuotientExistenceStatement` satisfy the flatness premise.
Neither quotient existence nor a theorem asserting its properness is
proved here.

For every rational point `x : Over.mk (𝟙 (Spec k)) ⟶ Q`, the conclusion
asks for an open `V : Q.left.Opens` with the following properties:

- `IsAffineOpen V`: the actual open subscheme is affine.
- `Set.range x.left ⊆ V`: it contains the scheme image of the rational point.
- The inverse images of `V` under the restricted action
  `(a.restrict i).hom : U.X ⊗ Q ⟶ Q` and the second projection coincide.

The last condition is equality of opens in the underlying scheme of the
product. It expresses invariance on all scheme points, including points
with nontrivial residue fields. Equivalently, on every scheme test, a
point of `Q` factors through `V` if and only if its translate by any point
of `U` does. In particular every rational translation preserves `V` and
its closed complement. The statement uses the Zariski opens of the actual
scheme `Q.left`; it puts no topology on the set of rational points.
Only neighbourhoods of rational points are asserted, which is the form
needed for a rational fixed point in an orbit closure.

## Provenance and remaining proof

This is a derived consequence of J. S. Milne, *Algebraic Groups* (2017),
Theorem 17.65 and the covering argument immediately after it, printed
pp.374–375 (zero-based PDF pages 389–390). The source works with the variety
of Borel subgroups, identified with `G/B`. It proves that, for each Borel
`B'` containing `T`, the set of Borels whose `T`-orbit closure contains
`B'` is open and affine. These opens cover the flag variety: each
`T`-orbit closure contains a `T`-fixed Borel. Transport along the actual
homogeneous quotient gives the neighbourhoods in this statement.

The source states stability for `I_u(T)`. The proof establishes it by
putting that subgroup in a parabolic `P` containing a Borel through `T`;
`P` preserves a line in the dual representation and thus its complementary
affine chart. The same argument applies to `U`, because the containment
premise places `U` in that Borel and hence in `P`. Preservation of the
complementary chart is preservation by an actual group-scheme action,
which gives the equality of inverse-image opens used here. No use of
normalization of `U` by `T` is needed. This is the same extension to an
arbitrary `U` explained in the published flag-step statement's Markdown.

Milne's proof of Theorem 17.65 uses the line-stabilizer realization of
Theorem 4.27, the projective attracting-cell results of Propositions 13.52
and 13.53, and the transitivity on Borels containing `T` from Proposition
17.53. The covering step uses the proper solvable fixed-point theorem
(Corollary 17.3). These are proof obligations, not premises silently
assumed proved by this module. A proof may follow a different route but
must establish the displayed proposition for the actual supplied quotient.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to these
passages. Worker 1489 formulated this interface in coordination with
Worker 1460's orbit-closure proof.
