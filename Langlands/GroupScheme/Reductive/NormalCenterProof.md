# Full centres of normal connected reductive subgroups

Worker 1360 assembled this proof; Worker 303 supplied the centralizer assembly
route and identified the published structural inputs.

`Langlands.GroupScheme.normalReductiveCenter` proves exactly the existing
`Langlands.GroupScheme.NormalReductiveCenterStatement.{u}` for arbitrary
universe `u`. For every field `k : Type u`, connected reductive group schemes
`G` and `H` over `Spec k`, and a closed normal inclusion `i : H ⟶ G`, it gives

```text
center H ≤ (center G).comap i.
```

Both centres are the full scheme-theoretic subgroup functors. Their definitions
quantify over every test scheme and every refinement, including nonreduced
tests. No smoothness or reducedness of either centre, field perfectness,
algebraic closedness, characteristic restriction, or further structural
premise is added. The statement and its imported definitions are unchanged.

The Lean proof composes published theorems. First,
`algClosedMaximalTorusCentralizer_fromQuotient` is applied to
`dynamicCentralizerReductive` and `solvableTorusQuotient`. These discharge its
two structural premises and prove the existing
`AlgClosedMaximalTorusCentralizerStatement.{u}`. This is equality of the full
torus centralizer with the torus range for every maximal torus of a connected
reductive group over an algebraically closed field. The assembly uses a generic
cocharacter and an actual closed centralizer representative; dynamic
reductivity makes that representative reductive, and the solvable quotient
theorem supplies the central-maximal-torus argument. No arbitrary-field
maximal-torus centralizer theorem is required.

The published `normalReductiveCenterCentralizerReduction` consumes that
algebraically closed statement and returns the exact target over every field.
Its proof passes to the algebraic closure, chooses a maximal torus there, and
uses self-centralization to contain the full centre of `H` in a closed split
torus. A closed representative of the centre factors through this torus.
Rigidity for closed subgroups of split tori makes the ambient connected
conjugation action on this representative trivial, with no smooth-centre
hypothesis. The published fpqc comparison then descends the centre containment
to the original field. This module discharges the reduction's remaining
structural premise; none remains in `normalReductiveCenter`.

The provenance is internal composition of these published Library results.
The target and the imported reduction document the connection with Conrad,
Gabber and Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition A.1.13, printed p.471 (PDF p.497, zero-based index 496),
registered as `conrad-gabber-prasad-2015-pseudo-reductive`. The implemented
route uses the published all-test rigidity and fpqc descent proofs rather than
reimplementing the source's argument with the étale automorphism functor.
