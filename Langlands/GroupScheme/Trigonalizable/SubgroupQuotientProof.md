# Proof: subgroups and quotients of trigonalizable groups are trigonalizable

Author: Worker 5157.

This module proves the published statement
`Langlands.GroupScheme.TrigonalizableSubgroupQuotientStatement.{u}` from
[`SubgroupQuotientStatement`](SubgroupQuotientStatement.md). It is Milne, *Algebraic Groups*
(2017), Corollary 16.3. The entry theorem is

```lean
theorem Langlands.GroupScheme.trigonalizableSubgroupQuotient :
    TrigonalizableSubgroupQuotientStatement.{u}
```

It works for every universe `u` and uses no hypotheses beyond those of the statement. The
proof uses the helper modules [`MatrixCriterion`](MatrixCriterion.md) and
[`CoalgebraCriterion`](CoalgebraCriterion.md). Milne argues with a faithful representation.
This proof instead passes through the coordinate bialgebra, in the same way as the Library's
proof that closed subgroups of unipotent groups are unipotent
(`UnipotentClosedSubgroupAssembly`).

## Closed subgroups

`IsTrigonalizable.of_isClosedSubgroup` takes a field `k`, group schemes `G` and `H` over
`Spec k` with `[IsAffineHom G.X.hom]`, a homomorphism `i : H ⟶ G` with `IsClosedSubgroup i`,
and `IsTrigonalizable G`. It concludes `IsTrigonalizable H`.

1. `G` is affine over the affine base, and so is `H`, because a closed immersion is affine.
   The published `AffineCoordinates.groupSchemeIso` identifies each of them with a
   corepresented group scheme on its coordinate algebra.
2. Conjugate `i` by these isomorphisms. The result is still a closed immersion, because the
   conjugating maps are isomorphisms of schemes. Express it through
   `Corepresented.pointsTrans` and `Corepresented.groupSchemeMap_pointsTrans`. The published
   `Chevalley.coordinateRestriction_surjective` then shows that the coordinate restriction
   bialgebra map `Chevalley.coordinateRestrictionBialgHom` from the coordinates of `G` to
   those of `H` is surjective.
3. `IsTrigonalizable.of_iso` and `isTrigonalizable_iff_isMatrixTrigonalizable` turn
   trigonalizability of `G` into `IsMatrixTrigonalizable` for its coordinate bialgebra.
   `IsMatrixTrigonalizable.of_surjective` moves it to the coordinates of `H`. The same two
   results, used in reverse, give `IsTrigonalizable H`.

The finite-type hypothesis of the statement is not used in this part.

## Quotients

Let `q : G ⟶ Q` have flat and surjective underlying morphism of schemes.
`IsTrigonalizable.of_flat_surjective` gives `IsTrigonalizable Q` directly. A flat surjective
morphism is an epimorphism of schemes, so global functions on `Q` pull back injectively to
`G`. A stable line of the restriction of a representation of `Q` to `G` is therefore already
a stable line for `Q`. The finite-type and affineness hypotheses on `G` and `Q` are not used in
this part.

## Assembly

`trigonalizableSubgroupQuotient` introduces `k`, `G` and the hypothesis
`IsTrigonalizable G`. It proves the subgroup half with
`IsTrigonalizable.of_isClosedSubgroup`. For the quotient half, it turns the hypotheses
`Flat q.hom.hom.left` and `Surjective q.hom.hom.left` into instances and applies
`IsTrigonalizable.of_flat_surjective`.
