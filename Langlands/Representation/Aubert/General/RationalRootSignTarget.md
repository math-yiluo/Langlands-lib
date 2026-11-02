# Actual root signs and the relative Coxeter indexing

This internal comparison layer formulates the root-sign realization still needed
by the general Aubert consumer. It uses actual characters, the actual simple-root
subtype, and the actual quotient of the torus-image normalizer by its full
centralizer. Its realization propositions are targets, not proved structure
theorems. The conditional set-theoretic consequences below are proved.

The source is Renard, *Représentations des groupes réductifs p-adiques*, version
of 9 July 2026, V.4.1 and V.4.6, printed pp.118 and 120–121 / PDF pp.124 and
126–127. V.4.1 names the full-centralizer quotient and the reflections associated
to the simple relative roots. In V.4.6 the minimal representatives are described
by actual positive-root images, and the proof explicitly uses the equivalence
between right length increase and positivity of the image of a simple root.
The comparison of reflection conjugacy with equality of positive simple-root
images is an internal formulation of the required compatibility of those labels
with the character action; it is not a separately numbered assertion in Renard.

All declarations are in
`Langlands.Aubert.General.RationalPointFamily`. The conditional constructions
work over an arbitrary field `k`, with a commutative group scheme `T`, a group
scheme `G` with affine structure morphism, a monomorphic `i : T.toGrp ⟶ G`,
and any cocharacter `ν`. They take the two exact premises
`HasPointNormalizerComparison i` and `HasPointCentralizerComparison i`.
The action is the existing `weylCharacterAction i hN hZ`, with inverse pullback
on characters and the same ambient normalizer representatives. These two
subgroup comparisons are not established here.

The index `SimpleRoot i ν` is literally the membership subtype of
`simpleRelativeRoots i ν`. A supplied `Fintype` of that subtype permits the
following finite constructions; no instance is manufactured by an assumption
of the desired root-sign result.

- `rootPositiveSimpleSet` consists of the simple characters whose images under
  the actual action lie in `positiveRelativeRoots i ν`.
- `rootSimpleImage w I` consists of those actual simple characters equal to
  the image of some member of `I`. Its character equality retains the sign.
- `RootMapsIntoSimple w I J` requires every member of `I` to have its actual
  character image in `J`. Thus there is no silent omission of a non-simple
  image.

The two membership lemmas unfold the finite filters.
`rootSet_rootSimpleImage` proves that the character set of `rootSimpleImage`
is the image of `rootSet I` intersected with the actual simple-root set. Its
proof unpacks the two subtype-image witnesses in each direction.
`rootSet_rootSimpleImage_of_mapsIntoSimple` removes that intersection when
every image is accounted for in a specified simple-root subset. Its proof
uses the supplied target witness to show the image already consists of simple
roots.

For a Coxeter matrix on exactly `SimpleRoot i ν` and a Coxeter system `cs`
on exactly `Weyl i`, the separately named comparison predicates are:

- `RootLengthComparison`: for every `w` and simple character `a`, the strict
  inequality `length w < length (w * simple a)` holds exactly when the actual
  character image of `a` is a positive relative root.
- `PositiveSimpleReflectionComparison`: provided that actual image is positive,
  `w * simple a * w⁻¹ = simple b` holds exactly when the actual character image
  of `a` equals the simple character `b`.

The positivity premise in the second predicate is essential. Reflection
conjugacy alone does not distinguish a root from its negative. This module
does not equate the intrinsic `simpleImage` with the actual character image
for arbitrary inputs.

`positiveSimpleSet_eq_rootPositiveSimpleSet` follows from the length comparison
by extensionality of the two finite filters.
`rootSimpleImage_eq_simpleImage_of_positive` and
`rootMapsIntoSimple_iff_of_positive` require positivity of every source image.
Their proofs apply the second comparison to each source and target witness.
The latter preserves the universal requirement that every source image occurs.

`rootSet_associatedSubset` additionally assumes the separately named intrinsic
propositions `minimalityLengthCriterion cs` and `associatedSubsetLaws cs`,
and supplied finite enumerations of both the simple-root subtype and `Weyl i`.
Its conclusion identifies the character set of `associatedSubset cs J` with
the actual image of `rootSet J` under the **inverse** of `longestRep cs J`.
The proof inverts the existing minimality witness for that longest representative
in `D(J,∅)`, applies the minimality/length criterion to obtain right length
increase on every member of `J`, and then applies `RootLengthComparison` to
obtain positivity. The intrinsic associated-subset proposition supplies all
reflection-label images. The conditional positive-image comparisons turn
these into actual character images, so the preceding set equality applies.
No intrinsic assertion is proved by assuming it as part of an unnamed package.

`HasRootSignCoxeterRealization` is the proposition that there exist a Coxeter
matrix and a Coxeter system with exactly that actual index type and actual
quotient group, satisfying both named comparisons. It contains no
representation-theoretic identity.
`RationalRootSignCoxeterStatement` universally asks for this realization for
connected reductive groups over nonarchimedean local fields, a maximal split
torus, and a generic cocharacter, conditional on both exact point comparisons.
It uses `Field`, `ValuativeRel`, `TopologicalSpace`, and
`IsNonarchimedeanLocalField`, with no characteristic-zero restriction.
The affine and monomorphism instances follow from the explicit reductive and
maximal-split-torus hypotheses. The statement has no nonempty-root hypothesis.

Neither proposition is proved. General root-system existence, finiteness,
the two point comparisons, this Coxeter/root-sign realization, standard-Levi
Weyl generation and intersection/conjugation comparisons remain distinct
structural obligations. Existing conditional finiteness helpers are to be
reused separately. No actual Levi subgroup equality, topology property,
classification input, normalized functor comparison, Weyl-conjugacy of induced
classes or Aubert identity is asserted by this unit.
