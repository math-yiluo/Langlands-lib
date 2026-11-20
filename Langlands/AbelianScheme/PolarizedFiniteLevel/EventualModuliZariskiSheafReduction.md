# The eventual Zariski sheaf property from Lefschetz's theorem and gluing

This unit derives the published statement `EventualModuliZariskiSheafStatement` from two
statements:

- `CubicFieldEmbeddingStatement.{0}`: Lefschetz's embedding theorem for the cubic bundle
  of a datum over a field (published, unproved; Task 7747);
- `ModuliZariskiSheafOfRigidityStatement`: at a fixed level `n ≥ 3`, triviality of all
  polarized automorphisms over all level bases implies that the moduli functor is a
  Zariski sheaf (new in this unit's companion module).

## Declaration

`eventualModuliZariskiSheaf_of_rigidity` (proved definition): from proofs
`hL : CubicFieldEmbeddingStatement.{0}` and `hG : ModuliZariskiSheafOfRigidityStatement`
it produces a proof of `EventualModuliZariskiSheafStatement`, with the bound

`N = (cubicProjectiveDimension g d + 1) * (6^g * d * g!) + 1`,

that is `(6^g d) * (6^g d g!) + 1` for positive `d`. It is a `def` whose type is the
proposition `EventualModuliZariskiSheafStatement`, so it records an implication between
the three statements and proves none of them by itself.

## Proof

Fix `P`, `g > 0`, `d > 0` and take `N` as above. Let `n ≥ N` and `hn : 3 ≤ n`; then
`(cubicProjectiveDimension g d + 1) * (6^g d g!) < n`. Apply `hG P g d n hd hn`. Its
rigidity hypothesis holds: for a level base `S`, the level `n` is a unit in `Γ(S, ⊤)`
(`LevelBase.level_isUnit`), so `PolarizedIso.eq_refl_of_cubicFieldEmbedding`
(`GeometricPointRigidity`), applied to `hL` and the size inequality, makes every
polarized automorphism of every datum over `S` the identity.

## Provenance

Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition (1994), prove
fine representability at large level (Theorem 7.9, printed p.139, PDF p.152) from the
count of torsion points on hyperplanes (Proposition 7.7, printed p.138, PDF p.151) and
its consequence Corollary 7.8. The Library route uses the same count to prove triviality
of polarized automorphisms (`CanonicalCubicRigidity`, `GeometricPointRigidity`) and
derives the sheaf property by gluing; this split, and the bound `N`, are internal and
not claimed to be Mumford's. The remark after Theorem 7.9 notes that `n ≥ 3` suffices by
Serre's lemma, which this unit does not use.
