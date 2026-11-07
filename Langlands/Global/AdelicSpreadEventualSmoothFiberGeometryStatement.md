# Smooth fibre geometry after an actual arithmetic enlargement

This is a derived arithmetic specialization of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2) and Remark 3.5, and the spreading steps in the first
and third proof paragraphs of Theorem 4.5 on printed p. 12. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Fix an actual outside-`S` integer ring, two finite-type schemes `X` and `Y`
over that ring, and a morphism `f` over the same ring. Each of the following
properties holds for its actual generic-fibre map if and only if it holds
after base change to the actual outside-`T` integer ring for some finite
superset `T` of `S`:

1. Smoothness.
2. For a prescribed natural number `d`, every actual residue-field fibre is
   nonempty, geometrically connected, and of pure dimension `d`.
3. The conjunction of the first two properties, at one common enlarged
   level `T`.

The third assertion requires a common level, rather than two independently
chosen levels. `⊓` in its Lean expression is the pointwise conjunction of
morphism properties. The dimension may be chosen before the models or
morphism; it is fixed across all fibres of the morphism in that clause.

`CurvePlaceSpreadEventualPropertyStatement P` and
`NumberFieldSpreadEventualPropertyStatement P` are proposition templates
for the displayed equivalence. The file does not assert descent for
arbitrary `P`. The two named smooth-fibre-geometry statements instantiate
the templates with exactly the three properties above.
`AdelicSpreadEventualSmoothFiberGeometryStatement` is the conjunction of
these two arithmetic statements in arbitrary common universe `u`.

The function-field clause retains a perfect constant field `k`, the
original field `F`, its specified compatible `k` and `RatFunc k` algebra
structures, the scalar tower, and `FunctionField k F`. It uses the actual
`AlgebraicCurve.Place k F` and `curvePlaceSIntegers` rings. No finite-constant
or separability hypothesis is added. The number-field clause retains every
number field `K`, its actual finite places, and the original subrings
`(S : Set (FinitePlace K)).integer K`. All finite initial sets, including
empty ones, are allowed. Empty initial sets are a derived extension of
Conrad's nonempty-set convention, using the same finite-superlevel argument.
Infinite number-field places require no change to the integer-ring
inclusions.

Finite type is expressed by `LocallyOfFiniteType` and `QuasiCompact` on
both structure morphisms. Neither model is required affine or separated.
Every displayed map is the actual map produced by `Over.pullback` along
the literal integer-subring inclusion into the original field or the
larger integer ring. No replacement rings or abstract place systems occur.
The fibre predicate is the published
`NonemptyGeometricallyConnectedPureDimensionFibers`: it quantifies over all
actual target points and their scheme-theoretic residue-field fibres.
Pure dimension means that every actual irreducible component has
topological Krull dimension `d`. Empty fibres are excluded. If the target
is empty, the fibre assertion is vacuous.

The specialization is justified by the published colimit descriptions of
the original fields and the noetherianity of the initial integer rings.
Finite-type models over these rings are finitely presented and
quasi-separated, so the source's finite-presentation hypotheses apply.
The published smoothness and geometric-fibre descent results supply the
separate equivalences. Stability of both properties under actual base
change then permits a common finite enlargement for the conjunction; that
common-enlargement argument is a proof obligation, not a hypothesis.

This unit states the three equivalences. It does not construct a model
for an arbitrary field morphism, choose a common dimension on target
components, prove Lang–Weil or integral-point surjectivity, or assert
adelic openness. Those consumers and the proof of this statement remain
separate obligations.
