# Relative local dimension under arbitrary scheme base change

Worker 105 states Stacks Lemma 29.29.3(1) and the resulting equality of
actual source sublevels, as a prerequisite for the retrocompactness
argument of Lemma 29.29.6 and Conrad Theorem 3.4(2).

`RelativeDimensionBaseChangeInvariance` quantifies over four actual
schemes and a cartesian square

```
P --a--> X
|        |
b        f
|        |
v        v
Y --g--> Z.
```

The only finiteness assumption is that `f` is locally of finite type.
For every point `x` of `P`, the relative local dimension of `b` at `x`
equals that of `f` at `a x`. For every natural number `n`, the set of
points of `P` where this dimension is at most `n` is exactly the inverse
image under `a` of the corresponding source sublevel for `f`.

Relative dimension is the existing `relativeTopologicalKrullDimAt`, the
minimum dimension of open neighbourhoods of the canonical point in the
actual scheme-theoretic residue-field fibre. It is local topological
dimension, rather than the dimension of the local ring at that point.
The sublevels are the existing `relativeDimensionSublevel`, not additional
data or predicates supplied to the statement.

The schemes share Mathlib's scheme universe `u`. The base morphism `g`
is arbitrary. No affineness, separatedness, quasi-separatedness,
quasi-compactness or finite-presentation assumption is added. The
assertion includes empty schemes and nonsurjective base changes.

The pointwise equality is the original Stacks Lemma 29.29.3(1), with its
sides reversed. The sublevel equality is its immediate set-theoretic
consequence; this explains the derived provenance of the grouped target.
The source is registered as
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
Section 29.29, Lemma 29.29.3(1). That lemma's proof reduces the
pointwise equality to Algebra Lemma 10.116.6.

This file states a proposition. Its proof, sublevel retrocompactness,
geometric-connectedness constructibility, Conrad's filtered descent
and whole-paper coverage remain separate obligations.
