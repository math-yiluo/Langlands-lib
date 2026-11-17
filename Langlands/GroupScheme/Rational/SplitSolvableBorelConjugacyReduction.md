# Split Borel conjugacy: reduction to a connected ambient group

Worker 755. Internal proof helpers for the proof of
`Langlands.GroupScheme.SplitSolvableBorelConjugacyStatement`
([`SplitSolvableBorelConjugacyStatement`](SplitSolvableBorelConjugacyStatement.md)), Milne,
*Algebraic Groups* (2017), Theorem 17.105(a),(b), pp.384–385. The module adds no definitions
and no statements. It proves the full statement from its clause (a) for connected ambient
groups, which is taken as a hypothesis. It also proves three lemmas used on the way, all in the
namespace `Langlands.GroupScheme.SplitSolvableBorelConjugacy`.

## Provenance

Milne states Theorem 17.105 for a group variety `G` that need not be connected. The Borel
subgroups in it are those of the identity component `G⁰` (see the Markdown of the statement).
Milne's proof of (a) uses the complete variety `G/B`. The Library's properness theorem for
parabolic quotients assumes a connected ambient group, so the proof first moves to `G⁰`. Milne
derives (b) from (a) "because all Borel subgroups have the same dimension". The Lean proof
instead uses the maximality clause of `IsBorelSubgroup` for the second Borel subgroup. The
lemmas below are internal steps of this proof and have no separate source.

## Declarations

- `isGeometricBorelSubgroup_factor G hb`. Let `G` be smooth and affine over `k`, let `B` be
  connected, and let `b : B ⟶ G` be a geometric Borel subgroup. Then the factorization
  `IdentityComponent.factor G b : B ⟶ G⁰` is a geometric Borel subgroup of `G⁰`.
  *Proof.* `IsBorelSubgroup.of_comp`, applied to the closed inclusion `G⁰ ⟶ G`, gives the Borel
  property over `k`. Over the algebraic closure, the base change of `b` is the base change of
  the factorization followed by the base change of the inclusion
  (`Functor.map_comp`, `IdentityComponent.factor_identityComponentι`). The base-changed inclusion
  is a closed immersion (a published instance in `IdentityComponent`, stated for
  `specMap (algebraMap k (AlgebraicClosure k))`, which is `toAlgebraicClosure k` by definition).
  So `IsBorelSubgroup.of_comp` applies again.
- `exists_range_le_of_identityComponent G h g₀ hg₀`. Suppose `B` and `H` are connected and the
  `k`-point `g₀` of `G⁰` satisfies
  `range (factor G h) ≤ range (factor G b ≫ int_{G⁰}(g₀))`. Then
  `range h ≤ range (b ≫ int_G(g₀ ≫ ι))`, where `ι : G⁰ ⟶ G` is the inclusion. *Proof.*
  Postcompose the inclusion with `ι` (`SubgroupFunctor.range_comp_mono`). Then rewrite with
  `factor ≫ ι = id` and with `innerIso_hom_comp`, which says `int_{G⁰}(g₀) ≫ ι = ι ≫ int_G(g₀ ≫ ι)`.
- `range_eq_of_range_le hb hb' g hle`. Let `b` and `b'` be Borel subgroups (`IsBorelSubgroup`)
  of the same group with `range b' ≤ range (b ≫ int(g))`. Then the two ranges are equal.
  *Proof.* Both `c := b ≫ int(g)` and `b'` are closed immersions, hence monomorphisms.
  `SubgroupFunctor.factorOfRangeLE` gives `f : B' ⟶ B` with `f ≫ c = b'`. The group `B` is
  smooth, connected and solvable, and `c` is a closed subgroup. So the maximality clause of `b'`
  makes `f` an isomorphism. Then `c = inv f ≫ b'`, and `range_le_of_factor` gives the reverse
  inclusion.
- `splitSolvableBorelConjugacy_of_connected hconn : SplitSolvableBorelConjugacyStatement.{u}`.
  The hypothesis `hconn` is clause (a) of the statement with the extra instance argument
  `[ConnectedSpace G.X.left]`. Its quantifiers and argument order are otherwise those of the
  statement. *Proof.* Fix `k`, `G`, `b` and `B`. Split solvable groups are connected
  (`IsSplitSolvableGroupScheme.connectedSpace`), so `b` and every split solvable closed
  subgroup `h` factor through `G⁰`. The factorization of `h` is closed in `G⁰`
  (`IsClosedSubgroup.of_comp`), and the factorization of `b` is a geometric Borel subgroup of
  `G⁰` (`isGeometricBorelSubgroup_factor`). The group `G⁰` is smooth, affine and connected by
  published instances. Then `hconn` applied to `G⁰` gives `g₀`, and
  `exists_range_le_of_identityComponent` gives clause (a) for `G` with the `k`-point
  `g₀ ≫ ι`. For clause (b), let `b'` be a split Borel subgroup. It is a closed subgroup, so
  clause (a) gives `g` with `range b' ≤ range (b ≫ int(g))`, and `range_eq_of_range_le` turns
  this inclusion into the required equality.

The connected case of clause (a) is proved separately, as the theorem
`Langlands.GroupScheme.splitSolvable_borel_containment_connected`, and the final proof applies
`splitSolvableBorelConjugacy_of_connected` to it.
