# Proper maps on actual points over locally compact fields

Author: Worker 105.

The original source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points*, December 31, 2011, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source locator is the local-field reduction and its proof in Proposition
4.4, printed page 11. The main proposition concerns adelic points; the present
unit isolates the local result proved inside that argument and its immediate
absolute consequence. It makes no adelic properness claim.

`K` is an arbitrary field in an arbitrary universe with a Hausdorff, locally
compact topology and `IsTopologicalDivisionRing K`. The explicit argument
`hnondiscrete : ¬ DiscreteTopology K` expresses the standard nondiscreteness
convention for local fields. There is no valuation, characteristic, perfection,
archimedean or nonarchimedean restriction. In particular both real and complex
fields and all nonarchimedean local fields are within the intended scope. No
chosen norm, group structure on the scheme, projective embedding, Chow datum or
compactness certificate is an input.

`SchemePointLocalPropernessProperty K hnondiscrete` quantifies over actual
schemes `X` and `Y` over `Spec K`. Their structure morphisms are separated and
of finite type, expressed by `IsSeparated`, `LocallyOfFiniteType` and
`QuasiCompact`. For every actual relative morphism `f : X ⟶ Y` with
`IsProper f.left`, it asserts `IsProperMap` for actual postcomposition
`p ↦ p ≫ f`. Both point carriers are exactly the existing `RingPoint K X K`,
namely relative scheme morphisms from `Spec K`. Each topology is explicitly the
existing `schemePointTopology`, the final topology from actual affine open
charts with their algebra-map evaluation topologies. There is no topology chosen
on the underlying Zariski space in place of the point topology.

Mathlib's `IsProperMap` includes continuity and the usual topological
properness condition. On these locally compact Hausdorff point spaces it is
equivalent to continuity together with compact inverse images of compact sets.
The corresponding separation and local compactness properties of scheme points
are separate Library results, not hypotheses supplying the desired properness.

`ProperSchemeLocalPointCompactnessProperty K hnondiscrete` asserts compactness
of the same actual point space for every scheme whose structure morphism is
proper. Properness already entails the separation and finite type needed here.
This is the absolute consequence obtained by mapping to `Spec K`, whose relative
`K`-point set has one element. `LocalFieldProperPointProperties` is the conjunction
of the two assertions and is the focused proof target.

Nondiscreteness is essential in this interpretation of the source's locally
compact field convention. For an infinite discrete field, every affine chart of
projective one-space has discrete evaluation topology, so its chart-final point
topology is discrete. Its infinitely many rational points cannot form a compact
space. Such a field is excluded explicitly, rather than silently strengthening
or misreading the source statement.

Conrad proves the local proper-map assertion by first treating projective maps,
then applying Chow's lemma and induction on the dimension of the reduced
irreducible source. The properness of the underlying map of Zariski topological
spaces alone does not prove this assertion about rational-point topologies.
These declarations are Prop-valued statements and do not provide this proof.
The nonaffine and nonprojective cases remain part of the target. Proper maps of
algebraic spaces, the adelic conclusion of Proposition 4.4, and the model
stabilization conclusion remain separate obligations of the whole-paper task.
