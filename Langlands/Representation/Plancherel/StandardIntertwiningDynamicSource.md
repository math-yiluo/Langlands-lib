# Source-normalized quotients for actual dynamic radicals

This is an internal derived adapter for standard intertwining integration. The
motivation is Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), I.1, printed p.240 / PDF page 6, and IV.1,
printed p.279 / PDF page 45, with the rational composition identity IV.1(12),
printed p.283 / PDF page 49. I.1 normalizes intrinsic subgroup Haar measures
using one special compact subgroup. IV.1 orders the complementary unipotent
factors before passing to rational intertwining operators. The present unit
specializes the existing source-scale quotient construction to actual dynamic
subgroups. Its cover deductions and quotient selection are internal results;
it does not assert the full rational identity or realize the requisite ordered
charts for general reductive parabolics.

The Lean namespace is
`Langlands.Plancherel.StandardIntertwining.DynamicSource`.

## Actual groups and topology

Let `k` be any nonarchimedean local field and `G` an affine group scheme locally
of finite type over `Spec k`. The ambient group is the actual
`RationalPoint k G.X` with `rationalPointTopology k G.X`. For a cocharacter
`χ : Gm ⟶ G`, write `Uχ = unipotentPoints χ`, the literal rational-point
subgroup of `Dynamic.unipotent χ`. The hypotheses do not require characteristic
zero, splitness, quasisplitness, or a representation-theoretic condition.
Connected reductive groups lie within this affine finite-type setting.

The existing rational-point theorems supply the topological-group, Hausdorff
and local compactness properties. For the composition application,
`RationalPointFamily.affineRationalPoint_nonarchimedeanGroup`,
`localField_secondCountableTopology` and
`rationalPoint_secondCountableTopology` supply the open-subgroup-basis and
second-countability properties in that same topology. None of these properties
is a caller-supplied premise here. The individual measurable spaces and their
`BorelSpace` instances remain explicit throughout.

One ambient compact open subgroup `Q`, together with its compactness proof,
is supplied. The construction does not establish that `Q` is the special
maximal compact of the source, or that it has the local product properties
needed below.

## Proven covers and exact quotient measures

The private helper `dynamicCover` applies the published
`BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup` to a
singleton. Thus every element of `Uχ` lies in a compact open subgroup of
`Uχ`. This is the genuine covering property used in the source-scale
construction, not merely a neighborhood basis at the identity. The published
`isClosed_unipotentPoints` supplies closedness of each `Uχ`.

The private helper `closedSubgroupCover` treats a closed ambient subgroup
`H ≤ Uχ`. Its actual inclusion `H →* Uχ` is a closed embedding: composing
with the ambient subtype inclusion is the closed inclusion of `H`, and
closed-embedding cancellation gives the claim. Pulling a containing compact
open subgroup back along this inclusion gives a compact open subgroup of `H`
containing the original element. Compactness follows from the closed
embedding's compact-preimage theorem; openness follows from continuity.
No new contraction proof is used.

`quotientMeasure Q hQ χ ψ` is the existing `sourceQuotientMeasure` specialized
to these proved closedness and covering facts. Its carrier is the actual left
quotient `(Uχ.subgroupOf Uψ) \ Uψ`; normality is unnecessary. The two source
measures are exactly `subgroupCompactOpenHaar` on `Uψ` and
`sourceIntersectionHaar` on `Uχ.subgroupOf Uψ`, normalized at their actual
ambient-`Q` preimages. They are intrinsic subgroup Haar measures.

`quotientMeasure_isCompatible` exports the full complex Weil compatibility
property for this exact quotient and those exact source measures. In
particular it includes right quotient-translation invariance, regularity,
nonzero mass, integrability of quotient averages of compactly supported
continuous complex functions, and the Weil formula.
`quotientMeasure_regular` and `quotientMeasure_ne_zero` export its regularity
and nonzero consequences. The local right-invariance instance in the theorem
is proved from the cover; it is not an additional hypothesis.

For three cocharacters and supplied
`D : OrderedSubgroupFactorization Uχ₀ Uχ₁ Uχ₂ V W`,
`nestedQuotientMeasure Q hQ χ₀ χ₁ χ₂ D` specializes the existing
`sourceNestedQuotientMeasure`. Its ambient carrier is `Uχ₁.subgroupOf Uχ₂`,
and its kernel is
`(Uχ₀.subgroupOf Uχ₂).subgroupOf (Uχ₁.subgroupOf Uχ₂)`.
The ambient measure is the exact `sourceIntersectionHaar` and the kernel
measure is `D.sourceNestedKernelHaar`, at the same ambient source scale.
`nestedQuotientMeasure_isCompatible`, `nestedQuotientMeasure_regular` and
`nestedQuotientMeasure_ne_zero` give the corresponding full compatibility,
regularity and nonzero results. The underlying constructors choose measures
only from the published compatible-measure existence theorem, using the
proved covers and closedness. No quotient-existence or compatibility premise
is added to this interface.

## Conditional actual integral composition

`comp_hasIntegral` retains the supplied ordered chart datum `D` and closedness
of the actual ambient complements `V` and `W`. The datum includes three
multiplication homeomorphisms for the first, second and direct ordered
factorizations, with their actual ambient multiplication formulas. It is
not a commuting direct-product group decomposition.

The cover of `V` is derived through `D.first_le : V ≤ Uχ₁`; that of `W` is
derived through `D.second_le : W ≤ Uχ₂`. Together with the three singleton
radical covers, these supply all five original-cover premises of
`D.comp_hasIntegral_at_sourceQuotients`. All three radical closedness premises
are proved as above. The caller still supplies the following three separate
local Cartesian image identities, with every compact open pulled back from
that same `Q`: the identity for `D.firstSubgroupProduct`, the one for
`D.intersectionSubgroupProduct`, and the one for `D.secondSubgroupProduct`.
They are not consequences of the existence of a global ordered chart.

The representation `A` is the canonical `SmoothRep` of a common Levi `M`,
with the representation-carrier universe independent of the field/point
universe. The two semidirect decompositions `h₀` and `h₁` are supplied.
The quotient choices precede the integral witnesses in the theorem's type:
`hf` integrates `f` to the evaluation of the intermediate induced section
`F`, at `quotientMeasure Q hQ χ₀ χ₁`; `hF` integrates that same `F` to `J`,
at `quotientMeasure Q hQ χ₁ χ₂`. The remaining `ha` is ordered scalar
integrability of `f` against every smooth functional on the original carrier,
using intrinsic source Haar on `V` and `W`, with evaluation at `(v*w)*g`.
The conclusion is the actual direct `HasIntegral` for `f` and that same `J`,
at `quotientMeasure Q hQ χ₀ χ₂`.

The proof instantiates `D.comp_hasIntegral_at_sourceQuotients` with the proved
closedness and covers, passing the three local identities and all analytic
witnesses unchanged. Its constructed nested quotient is definitionally the
one above. No measure is substituted into an existing witness, and no
scalar correction is hidden in the conclusion.

This unit discharges actual radical topology, closedness, covers and quotient
construction for the displayed setting. Ordered-chart realization, the three
local product identities, special-compact realization, analytic convergence,
original-carrier representability and rational continuation remain separate
obligations. No whole-task Plancherel completion condition is closed here.
