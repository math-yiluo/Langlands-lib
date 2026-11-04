# Corrected logarithmic comparison for normalized-exponent temperedness

`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedLogarithmicComparisonStatement`
is a derived proposition comparing the published normalized-exponent
temperedness predicate with an explicit all-point logarithmic formula.
This pair states the comparison and does not prove it.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are V.3.14–V.3.15, printed p.113/PDF p.119
(restricted-root combination cones), V.3.19–V.3.20, printed pp.115–116/PDF
pp.121–122 (real parameters), VII.1.1, printed p.220/PDF p.226
(normalized Jacquet exponents), and VII.2.1, printed p.227/PDF p.233
(temperedness). This comparison repairs the logarithmic formula while keeping
the existing positive valuation and the explicitly chosen `q^(-s)` convention.
It is an internal derivation from these constructions, rather than a verbatim
assertion printed in the book.

## Exact assertions

Fix an arbitrary connected reductive group scheme `G` over a nonarchimedean
local field `k` and a smooth complex representation `π`. Write
`q = LocalField.residueCardinality k`. For every actual parabolic map
`p : P ⟶ G`, rational Levi map `l : M ⟶ P`, and split-component map
`a : A.toGrp ⟶ M`, with their respective witnesses `hp`, `hl`, and `ha`,
the first conjunct quantifies every compatible
`pres : ParabolicRootPresentation p l a`, every represented geometric
unipotent radical `r : U ⟶ P`, every witness that
`subgroupMultiplication l r` is an isomorphism, and every character `χ`
which is an actual `IsNormalizedJacquetExponent` for those data.
For each such exponent it states both equivalences:

1. `normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.nonnegCone`
   if and only if there is `φ : RealTorusSpace.Vstar A` in that same cone
   such that, for every actual point `t : rationalPoints A.toGrp`,
   `Real.log ‖(χ t : ℂ)‖ =
   (-Real.log (q : ℝ)) * RealTorusSpace.pair A φ (valuation hA t).toAdd`,
   where `hA = ha.isCentralSplitTorus.1.1` and `valuation` is the published
   `Plancherel.SplitTorus.valuation`.
2. The same normalized cone membership holds if and only if
   `-rawLogRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.nonnegCone`.

The second conjunct is the complete predicate equivalence.
`IsNormalizedExponentTempered hG π` holds if and only if `π` is admissible
and, for every actual parabolic, rational Levi and split-component triple,
there is a compatible presentation and every compatible presentation,
every matching represented radical and decomposition witness, and every
actual normalized Jacquet exponent passes the existential-`φ` logarithmic
test above. Presentation existence is an explicit `Nonempty` conjunct
before the universal tests. It remains required when there are no
exponents. Neither one chosen presentation nor an empty family can
replace that coverage requirement.

The cone is the published nonnegative span of the presentation's actual
restricted simple roots in the **full** real character space of `A`.
Thus the same span and central-direction constraint occur on both sides.
It is not the separate chamber defined by coroot inequalities.
The exponent predicate uses the actual normalized Jacquet coinvariant
representation and its nonzero smooth generalized weight spaces. Openness
of the character kernel is already part of that predicate; this statement
adds no smoothness premise for `χ`.

## Normalization and scope

The source first defines the real part using a complex exponential based
on `q^(-s)`, then writes the raw natural logarithm of the modulus for it.
The existing positive valuation makes these different real functionals:

`rawLogRealPart hA χ = (-Real.log (q : ℝ)) • normalizedRealPart hA χ`.

The proposed repair divides the raw logarithmic functional by `-log q`
before applying the unchanged nonnegative root cone. Since `q > 1`,
`log q > 0` and
`-rawLogRealPart hA χ = Real.log (q : ℝ) • normalizedRealPart hA χ`.
This explains the minus sign in the second equivalence. The first
equivalence states the corresponding corrected all-point formula with
the exact factor `-log q`. It does not assert membership equivalence
between the raw and normalized parameters themselves in the same cone.

The canonical rational-point topology is installed explicitly, as in
the published exponent and temperedness interfaces. The field topology
is assumed Hausdorff; the ambient point group is assumed locally compact
and nonarchimedean. Connected reductivity supplies affineness, smoothness,
and hence local finite type for the actual cone construction. The field
has either characteristic allowed by `IsNonarchimedeanLocalField`.
The field and group use universe `u`, and the representation carrier
uses independent universe `v`. There is no ambient split-group
restriction, irreducibility assumption, scalar central character,
nonzero-carrier hypothesis, or finite-dimensional-carrier restriction.

## Proof and source obligations retained

The imported `SplitTorusNormFormula` supplies the all-point normalized
and raw pairing formulas and uniqueness through the actual valuation
image. These give a proof route for the first local equivalence.
Positive scalar closure of `pres.nonnegCone`, applied to `log q` and its
inverse, gives a route for the second. Applying the first equivalence
under the unchanged quantifiers gives the complete predicate comparison.
This describes a proposed route; no such proof is included in this pair.

Even after this comparison is proved, it will not construct the full
complex exponential map, prove its surjectivity, determine its period
lattice, or identify its arbitrary complex lifts with this real parameter.
Those portions of V.3.20 remain separate. Global presentation existence,
independence under every root choice, split-component transport, standard
reduction, full-group and full-center consequences, the Casselman
implication, and later induction and classification results also remain
separate obligations. In particular, this proposition preserves
presentation existence on both sides and does not prove it.
