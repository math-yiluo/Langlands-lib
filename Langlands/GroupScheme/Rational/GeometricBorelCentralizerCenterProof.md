# Proof: the centralizer of a Borel subgroup over an arbitrary field

Worker 739. `Langlands.GroupScheme.geometricBorelCentralizerCenter` proves exactly the
published proposition `Langlands.GroupScheme.GeometricBorelCentralizerCenterStatement.{u}`
(module `Langlands.GroupScheme.Rational.GeometricBorelCentralizerCenterStatement`,
[Markdown](GeometricBorelCentralizerCenterStatement.md)) at an arbitrary universe `u`. The
statement pair and everything it imports are unchanged.

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`,
every group scheme `B` over `Spec k` and every `i : B ⟶ G` with `IsGeometricBorelSubgroup i`
(`i` becomes a Borel subgroup after base change to the algebraic closure), it gives:

1. on every test scheme `T` over `Spec k`, a point `x : T ⟶ G.X` lies in the centralizer
   `(SubgroupFunctor.range i).centralizer` exactly when `x = y ≫ i.hom.hom` for some point
   `y` of `center B`, that is `C_G(B) = i(Z(B))`;
2. `(SubgroupFunctor.range i).centralizer = center G` as subgroup functors, that is
   `C_G(B) = Z(G)`.

There are no further hypotheses: `k` need not be perfect or algebraically closed.

## Implemented proof

The proof applies four published Library theorems; it contains no new argument.

- `borelHomomorphismRigidity` (module `Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityProof`)
  proves `BorelHomomorphismRigidityStatement.{u}`, Milne's Proposition 17.21 over an
  algebraically closed field: two homomorphisms `G_R ⟶ G'_R` that agree on `B_R` are equal.
- `borelCentralizerCenter_of_homomorphismRigidity` (module
  `Langlands.GroupScheme.Absolute.BorelCentralizerCenterReduction`) turns it into
  `BorelCentralizerCenterStatement.{u}`, Milne's Proposition 17.22 over an algebraically
  closed field: `Z(B) ⊂ C_G(B) = Z(G)`. The proof term names this result `hCentralizer`.
- `borelCenterEqualityReduction` (module
  `Langlands.GroupScheme.Absolute.BorelCenterEqualityReduction`) proves
  `BorelCentralizerCenterStatement.{u} → BorelContainingSubgroupSelfNormalizerStatement.{u} →
  BorelCenterEqualityStatement.{u}`. It is applied to `hCentralizer` and to
  `borelContainingSubgroupSelfNormalizer` (module
  `Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerProof`; Milne 17.49, which
  contains the normalizer theorem 17.48). The result is `BorelCenterEqualityStatement.{u}`,
  Milne's Proposition 17.45 for geometric Borel subgroups over an arbitrary field: the points
  of `Z(G)` are exactly the images under `i` of the points of `Z(B)`.
- `geometricBorelCentralizerCenterReduction` (module
  `Langlands.GroupScheme.Rational.GeometricBorelCentralizerCenterReduction`,
  [Markdown](GeometricBorelCentralizerCenterReduction.md)) proves
  `BorelCentralizerCenterStatement.{u} → BorelCenterEqualityStatement.{u} →
  GeometricBorelCentralizerCenterStatement.{u}`. Applying it to the two previous results
  gives the target.

That reduction's Markdown describes its argument. In outline, point (2) comes from 17.22 over
the algebraic closure `k̄` by fpqc descent along `Spec k̄ ⟶ Spec k`: the base change of
`C_G(B)` lies in `C_{G_k̄}(B_k̄)`, which equals `Z(G_k̄)`, the base change of `Z(G)`, and
`Z(G)` is represented by a closed subgroup. Point (1) follows by rewriting `C_G(B)` as
`Z(G)` with point (2) and applying 17.45.

`geometricBorelCentralizerCenter` uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, 17.70, printed
p.376 (one-based PDF p.392): for a Borel subgroup `B` of a connected group variety `G` over
`k`, `Z(B) = C_G(B) = Z(G)`. The paragraph just before it in Section 17i says these statements
over `k` "can be deduced from the algebraically closed case" because "the formation of
centralizers and normalizers commutes with extension of the base field". Milne gives no
separate proof; he cites 17.22 (printed p.359, PDF p.375) and 17.45 (printed p.365, PDF
p.381). The Lean proof follows that route, as described above. The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` lists Chapter 17 corrections only on pp.360,
364 and 386, none of which concerns 17.21, 17.22, 17.45, 17.48, 17.49 or 17.70.
