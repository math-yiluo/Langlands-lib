# A common rational maximal torus for two parabolic subgroups

Authors: Worker 49 and Worker 59. Their independently accepted proofs of the
same target are represented by this single declaration. The common-torus and
geometry helpers are in [ParabolicIntersectionGeometryProof](ParabolicIntersectionGeometryProof.md).

`Langlands.GroupScheme.parabolicIntersectionTorus.{u}` proves exactly the
unchanged published proposition
`Langlands.GroupScheme.ParabolicIntersectionTorusStatement.{u}`, the first
assertion of Borel–Tits, *Groupes réductifs* (1965), Proposition 4.7, printed
p.88. Take any field `k : Type u`, a connected reductive group scheme `G` over
`k`, and two actual parabolic subgroup morphisms `j : P ⟶ G` and `j' : P' ⟶ G`.
The proof gives a commutative group scheme `T` over `k` and a morphism
`i : T.toGrp ⟶ G` with `IsMaximalTorus i`, so `i` is maximal in the ambient
`G`. It also gives actual group-scheme homomorphisms `f : T.toGrp ⟶ P` and
`f' : T.toGrp ⟶ P'` with `f ≫ j = i` and `f' ≫ j' = i`. The torus may be
nonsplit. There is no assumption on characteristic, perfectness or cardinality
of `k`, and no minimality assumption on the parabolics.

## Proof

The theorem is one application of the published conditional reduction
`parabolicIntersectionTorus_of_structural_inputs` from
`Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction`
(Worker 1329, with Worker 1349). It supplies proofs of all four of that
reduction's hypotheses:

- `maximalTorusExistence : MaximalTorusExistenceStatement.{u}`, existence of a
  rational maximal torus in a smooth affine group over a field (Library proof);
- `maximalTorusBaseChange : MaximalTorusBaseChangeStatement.{u}`, maximality
  of a closed torus in a smooth affine group is preserved and reflected by
  field extension (Library proof);
- `maximalTorusConjugacy : MaximalTorusConjugacyStatement.{u}`, conjugacy of
  maximal tori over an algebraically closed field (Library proof);
- `parabolicIntersectionGeometry : ParabolicIntersectionGeometryStatement.{u}`,
  proved in the helper module
  `Langlands.GroupScheme.Absolute.ParabolicIntersectionGeometryProof`. The
  actual pullback `pullback j j'` is smooth, it is connected after base change
  to `AlgebraicClosure k`, and that base change contains an ambient maximal
  torus.

Inside the reduction, `MaximalTorusExistenceStatement` chooses a rational
maximal torus of the smooth affine intersection `pullback j j'`. Base change
to the algebraic closure keeps it maximal there. Geometric conjugacy inside
the connected base-changed intersection compares it with the ambient maximal
torus from the geometry statement, so it is maximal in `G` over the algebraic
closure. `MaximalTorusBaseChangeStatement` then reflects ambient maximality
back to `k`. Composing the torus with the two pullback projections gives `f`
and `f'`, and the pullback square gives the two factorization equations.

The proof follows Borel–Tits' route: a maximum-rank intersection of the two
parabolics, then a rational maximal torus of that intersection. The geometric
inputs are, however, the Library's dynamic and Borel overgroup results rather
than Borel–Tits 4.5–4.6, as described in the helper module's Markdown. The
proof uses neither Borel–Tits 4.18 nor any rational Bruhat decomposition. The
target statement's Lean/Markdown pair and all of its imports are unchanged.
