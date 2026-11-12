# Reducedness of an actual universal rigidified Picard parameter

`Langlands.AbelianScheme.algClosedFieldRigidifiedPicardParameterReduced`
proves exactly the published proposition
`Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardParameterReducedStatement.{u}`.
The universe `u` is arbitrary. For every algebraically closed field `k`,
actual abelian scheme `A` over `Spec k`, parameter `P : Over (Spec k)` and
actual rigidified family `L : RigidifiedFamily A P`, the hypotheses are
all-test universality of `L` and `LocallyOfFiniteType P.hom`. The conclusion
is Mathlib's scheme predicate `AlgebraicGeometry.IsReduced P.left`.

## Group structure and its origin

`RigidifiedLineBundle.actualUniversalCommGrpObj` specializes the published
`universalCommGrpObj` construction to the following published theorems:

- `pullbackTensorComparisonIsIso`;
- `pullbackTensorUnitCoherence`;
- `explicitPullbackTensorAssociativity`;
- `tensorMonoidalLeftUnitorComparison`;
- `pullbackTensorSymmetry`;
- `locallyFreeRankOneIffTensorInvertible`;
- `pullbackTensorComposition`.

The tensor and pullback names are in `Langlands.Scheme.Modules`;
`locallyFreeRankOneIffTensorInvertible` is in
`Langlands.AlgebraicGeometry.Picard`. They are imported from the proof
modules listed in the Lean file and discharge every explicit coherence and
local-comparison argument of `universalCommGrpObj`. The resulting
`CommGrpObj P` uses the actual family and its universal property on every
test scheme, including nonreduced schemes.

`actualUniversal_unit_eq_trivialParameter` composes Mathlib's
`MonObj.one_eq_one` with the published `one_eq_trivialParameter`.
The next lemma,
`Langlands.AbelianScheme.actualUniversal_unit_point_eq_fullPicardOriginPoint`,
evaluates that equality at `IsLocalRing.closedPoint k`.
By the definition of `fullPicardOriginPoint`, this identifies the
constructed group's identity point with the point used by the local
dimension and tangent statements.

## Reducedness of the origin stalk

The three local helper theorems work over any field.
`rigidifiedPicardOriginTangentFiniteAndFinrankLe` uses
`Langlands.AbelianScheme.fieldUniversalRigidifiedPicardTangentH1` to obtain
a linear equivalence between the actual tangent module at the section
classifying the trivial family and the actual first relative cohomology
module of the structure sheaf. The published theorem
`Langlands.AbelianScheme.fieldStructureSheafH1DimensionBound` supplies
finite dimensionality and the bound by a specified relative dimension `g`.
The inverse equivalence transfers finite dimensionality, and equality of
finranks transfers the bound.

`rigidifiedPicardOriginStalkRegular` also takes the numerical inequality

```text
(g : WithBot ℕ∞) ≤ ringKrullDim
  (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL)).
```

It applies the regularity consequence of
`Langlands.Scheme.fieldPointTangentLocalRegularity` to this lower bound
and the tangent upper bound. The tangent section evaluates to the
published origin by definition. `rigidifiedPicardOriginStalkReduced`
then applies `Langlands.CommutativeAlgebra.regularLocalDomain` and
Mathlib's instance that a domain is reduced.

## Discharging the bounds and proving the target

The final theorem constructs the group object above and applies the
published `Langlands.GroupScheme.algClosedFieldReducedOfOrigin`.
After rewriting its identity point, it suffices to prove reducedness of
the stalk at `fullPicardOriginPoint`.

Geometric connectedness of `A.X.hom` over the field spectrum gives
`ConnectedSpace A.X.left`. The published
`Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension` then
produces a natural number `g` with `A.HasRelativeDimension g`.

Apply the published
`Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence` to
`A.toGrp`. Commutativity, smoothness, properness and geometric
connectedness come from the existing abelian-scheme structure. This
produces an actual ample line bundle `M` on `A.X.left`. The published
`Langlands.AbelianScheme.algClosedFieldAmpleTranslationStabilizerFinite`
gives finiteness of its rational translation stabilizer:

```text
Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
  Nonempty ((LineBundle.pullback
    (GroupScheme.translation A.toGrp x).left).obj M ≅ M)}.
```

The published
`Langlands.AbelianScheme.algClosedFieldRigidifiedPicardOriginDimensionLowerBound`
applied to this same `M` gives the required stalk-dimension lower bound.
The local reducedness helper completes the origin-stalk goal, and
`algClosedFieldReducedOfOrigin` concludes reducedness of all of `P.left`.
That imported theorem supplies the translation and Jacobson argument.

All geometric, cohomological, dimension, regularity and translation inputs
are imported unconditional theorems. The local helpers' numerical premises
are discharged inside the final theorem. Its type has no additional
outer hypothesis and retains arbitrary characteristic and dimension zero.
No existence of a universal parameter is asserted.

## Provenance and authorship

This is a derived composition of the named Library results. Its route
follows the dimension and tangent argument of Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Corollary (6.6), printed pp.90–91 (PDF pp.94–95), identifies the tangent
space with `H¹`; Proposition (6.15), printed p.94 (PDF p.98), supplies the
dimension bound; Theorem (6.18), printed p.96 (PDF p.100), combines them
with an ample bundle and finite kernel to prove reducedness of `Pic⁰`.
Proposition (3.17)(ii), printed pp.38–39 (PDF pp.42–43), supplies the
origin-to-group translation argument.

The source's Theorem (6.18) concerns the identity component. Reducedness
of the whole arbitrary universal parameter here is the derived conclusion
explained in the target's companion. The implemented proof establishes
regularity directly at the origin and uses the published generic
translation theorem. It constructs the group law from all-test
universality. It does not use a chosen dual or an identity-component
smoothness theorem. Provenance and constructions for the imported results,
including ample existence, remain in their published companions.

Worker 2781 assembled this exact-target proof and explanation from the
carried private draft. Worker 677 supplied the universal group and unit
adapter; Worker 453 supplied the origin-local and core assembly; Worker
432 contributed the earlier interface designs. Their contributions are
retained here. Authorship of the independently published imported proofs
is recorded in those proofs' companions.
