# Normal solvable subgroups of reductive groups from split torus quotients

Author: Worker 1378.

This module reduces the published target
`AlgClosedReductiveNormalSolvableTorusStatement.{u}` (module
`Rational.AlgClosedNormalSolvableTorusStatement`) to the published
`SolvableTorusQuotientStatement.{u}` (module
`Absolute.SolvableTorusQuotientStatement`), and proves the reduction. It
does not prove the quotient statement, so it does not discharge the target.

## The reduction statement

`AlgClosedNormalSolvableTorusFromQuotientStatement.{u}` is the Prop-valued
implication

```
SolvableTorusQuotientStatement.{u} →
  AlgClosedReductiveNormalSolvableTorusStatement.{u}
```

Both propositions are published and used unchanged, with the same universe
parameter:

- `SolvableTorusQuotientStatement`: over an algebraically closed field `k`,
  every smooth affine connected solvable group `H` has a closed subgroup
  `i : U → H` with `U` smooth, connected and unipotent and with normal range,
  and a morphism `q : H → D` onto a split torus `D` that is an fppf quotient
  with kernel range equal to the range of `i` (`RelativeRoot.IsFppfQuotient`);
- `AlgClosedReductiveNormalSolvableTorusStatement`: over an algebraically
  closed field, a smooth connected solvable closed subgroup `h : H → G` with
  normal range in a pseudo-reductive group `G` has `IsTorus H` and
  `IsCentral h`.

## The proof

`algClosedReductiveNormalSolvableTorus_of_quotient` proves the implication
through `AlgClosedNormalSolvableTorus.isTorus_isCentral_of_solvableTorusQuotient`.
Let `G` be pseudo-reductive over an algebraically closed field `k`, and let
`h : H → G` be a smooth connected solvable closed subgroup with normal range.

1. `G` is smooth, affine and connected, and `H` is affine because `h` is a
   closed immersion into an affine group (`IsClosedSubgroup.isAffineHom_source`).
   The hypothesis gives `i : U → H` and `q : H → D` as above.
2. Conjugation by a rational point `g` of `G` restricts to `H`.
   `range_comp_innerIso_le` shows that the range of `h ≫ inn(g)` lies in the
   range of `h`, by normality of the range of `h`. `conjRestrict` is the
   resulting factorization `H → H` through the closed immersion `h`
   (`SubgroupFunctor.IsRepresentedBy.factorHom`), and `conjRestrict_comp`
   records `conjRestrict g ≫ h = h ≫ inn(g)`.
3. `conj_mem_range_comp` shows that conjugation by `g` preserves the range of
   `i ≫ h` on every test scheme. The composite `i ≫ conjRestrict g ≫ q` from
   the unipotent `U` to the split torus `D` is trivial on all points
   (`IsUnipotent.comp_eq_one_of_isSplitTorus`). So the image of a point of `U`
   under `i ≫ conjRestrict g` lies in the kernel of `q`
   (`mem_range_kernelι_iff`), which is the range of `i`.
4. `isNormal_range_comp` upgrades this to all-test normality of the range of
   `i ≫ h` in `G`. The composite is a closed subgroup (`IsClosedSubgroup.comp`),
   so its normalizer has a closed representative `n`
   (`hasClosedRepresentative_normalizer_centralizer_range`). `G` is reduced
   because it is smooth over a field, so `range_le_of_algClosed_points` turns
   the rational-point containment from step 3, applied to `g` and `g⁻¹`, into
   `range (𝟙 G) ≤ range n`. The normalizer is then everything, and
   `SubgroupFunctor.isNormal_of_normalizer_eq_top` gives normality.
5. `i ≫ h` is a smooth connected unipotent closed subgroup of `G` with normal
   range, so `HasTrivialUnipotentRadical G` makes its range trivial. Since `h`
   is a monomorphism, the range of `i` is trivial
   (`SubgroupFunctor.range_comp_eq_bot_iff`).
6. So `q` is an fppf quotient by the trivial subgroup and is an isomorphism
   (`RelativeRoot.IsFppfQuotient.isoOfBot`). Hence `H` is a split torus
   (`IsSplitTorus.of_iso`) and a torus (`IsSplitTorus.isTorus`).
7. Viewing `H` as a commutative group scheme through `IsTorus.isCommMonObj`,
   the published `isCentral_of_isNormal_of_isSplitTorus` (module
   `Rational.NormalSplitTorusCentrality`) shows that a normal monic split
   torus in the connected group `G` is central, so `IsCentral h`.

The pattern of step 4 follows the published
`TorusGeneratedEnvelope.isNormal_of_isAlgClosed` in
`Rational.TorusGeneratedEnvelopeNormalityReduction`.

## Provenance

This is a derived internal reduction. Its route follows the proof of Milne,
*Algebraic Groups* (2017), Corollary 17.62(b), printed p.372, over an
algebraically closed field, as documented in the Markdown of the target:

- the unipotent kernel `H_u` of Theorem 16.33(a),(c), printed pp.335-336, is
  stable under conjugation by `G`, and so is trivial because `R_u(G) = e`;
- `H ≅ H/H_u` is then a torus;
- a normal torus in a connected group is central, Corollaries 12.37-12.38,
  printed p.244.

Milne obtains the stability of `H_u` from its maximality among unipotent
subgroups. The Lean proof uses instead the triviality of every homomorphism
from a unipotent group to a split torus, applied to the conjugate of `U`
composed with `q`. This module adds no new citation and no new external
structural assertion. The hypothesis is an explicit premise of the
implication and is not proved here.
