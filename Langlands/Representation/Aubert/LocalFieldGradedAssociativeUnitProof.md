# Proof of the associative and unit identities for graded induction

`Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` proves
exactly `Langlands.Aubert.LocalFieldGraded.LocalFieldGradedAssociativeUnitStatement.{uF,uV}`.
It keeps both universe parameters independent and adds no hypothesis. For
every `K : AllFieldBZ.LocalFieldPackage.{uF}`, every nonarchimedean local
field realization `T : K.TopologicalData` and every preservation witness
`h : LocalFieldBinaryProductExactLengthStatement.{uF,uV}`, it proves the three
identities for `m := multiplication T h` and `one := unit T` on the whole
graded group `GradedGrothendieckGroup T`, the direct sum over all natural
ranks of the exact Grothendieck groups. The unit is the class of the actual
trivial line `unitObject T` of \(\mathrm{GL}_0\). The witness `h` supplies
finite length and exactness for the binary product and its descent to
Grothendieck classes.

The final theorem is the triple
`⟨multiplication_assoc T h, multiplication_unit_left T h, multiplication_unit_right T h⟩`.
The two unit laws are proved in `LocalFieldGradedInductionUnit`.

## Rank zero

`rankZero_equiv_unit` shows that every irreducible `A` of
`GeneralLinear 0 K.Carrier` is equivalent to `unitObject T`. The group is a
subsingleton by `GeneralLinear.subsingleton_of_rank_eq_zero`. For a nonzero
vector `v` of `A`, the span map from the trivial line is an intertwining map,
nonzero, injective and, by irreducibility, surjective. The trivial line on
`ℂ` is then identified with the line on `ULift ℂ` of `unitObject T`.

`inclusion_zero_eq_smul` shows that every rank-zero exact class `x` satisfies
`k • unit T = inclusion T 0 x` for some integer `k`. By
`SmoothRep.irreducibleGrothendieckStatement`, the exact Jordan–Hölder
comparison, `x` is the image of a finitely supported function on irreducible
isomorphism classes. Induction on that function reduces the claim to one
generator; `realizeIrreducibles_generator_irreducibleIsoClass` identifies its
image with the class of an irreducible representative, and
`ofRepresentation_eq_of_equiv` with `rankZero_equiv_unit` identifies that
class with the unit.

## Associativity on actual classes

`assoc_on_objects` proves associativity for the classes in the summands of
ranks `a`, `b`, `c` of three actual finite-length representations `A`, `B`,
`C`.

- If one of `a`, `b`, `c` is zero, that factor is `k • unit T` by
  `inclusion_zero_eq_smul`. Bilinearity of `multiplication` and the two unit
  laws make both sides equal.
- If all three ranks are positive, `multiplication_homogeneous` and
  `binaryProduct_objects` turn each side into the class of an actual
  iterated binary normalized product, in the summands of ranks
  `(a + b) + c` and `a + (b + c)`. `positiveAssociativityEquiv` from
  `LocalFieldGradedPositiveAssociativity` is an equivalence between the first
  of these representations and the pullback of the second along
  `GeneralLinear.reindex (finCongr (Nat.add_assoc a b c))`.
  `inclusion_eq_of_rank_equiv` then gives equality in the graded group.

## Extension to the whole graded group

`graded_ext_objects` says that two linear maps on the graded group agree
once they agree on `inclusion T n (ofObject A)` for every rank `n` and every
actual finite-length `A`. It combines `DirectSum.linearMap_ext` with
`FiniteLengthGrothendieckGroup.hom_ext_object`. `multiplication_assoc`
applies it three times: first to the two sides as linear maps of `x`, with
`y` and `z` fixed; then, with `x` an actual homogeneous class, as linear maps
of `y`; and finally, with `x` and `y` actual homogeneous classes, as linear
maps of `z`. The last case is `assoc_on_objects`.

## Transitive declaration dependencies

Following the constants in the types and values of declarations from
`localFieldGradedAssociativeUnit` reaches 1,482 Library declarations in 131
modules, including the starting theorem. The inventory lists each name and
its defining module, gives the first dependency edge into each module, and
includes the diagnostic that computes the closure with
`Lean.ConstantInfo.getUsedConstantsAsSet`. Lean's axiom check reports
`propext`, `Classical.choice` and `Quot.sound`. [Declaration inventory](LocalFieldGradedAssociativeUnitDependencies.md)

### Ordered regrouping

From `localFieldGradedAssociativeUnit`, `multiplication_assoc` calls the
private `assoc_on_objects`, whose positive-rank branch uses
`positiveAssociativityEquiv`. That equivalence calls `regroupLeftPair` and
`regroupRightPair`, each of which uses `regroupingEquiv` to apply
`Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping`. The regrouping
proof uses the following four declarations directly. [OrderedProductRegroupingProof.lean](../../AllFieldBZ/Representation/Parabolic/OrderedProductRegroupingProof.lean)

| Declaration | Use in `orderedProductRegrouping` |
| --- | --- |
| `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv` | Reassociates the external tensor factors along the prescribed refinement. |
| `Langlands.AllFieldBZ.Parabolic.refinementCoordinatesNormalization` | Identifies the normalized induced-function spaces in composed and fine block coordinates using the matching positive modulus halves. |
| `Langlands.AllFieldBZ.Parabolic.normalizedRefinementInductionTransitivity` | Identifies iterated normalized induction with normalized induction from the composed parabolic by evaluation at the inner identity. |
| `Langlands.AllFieldBZ.Parabolic.refinedInductionTensor` | Identifies refined induction in the coarse Levi with the external tensor of the inner normalized inductions. |

- `refinementCoordinatesNormalization` assembles `modulus_of_coordinates`,
  `halfModulus_of_modulus` and `induction_of_halfModulus` in the namespace
  `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization`.
  `modulus_of_coordinates` reaches `BlockShape.flattenBlockEquiv` for the
  labels of the flattened shape and `composedLeviModulus_flattened` for the
  modulus calculation.
- `normalizedRefinementInductionTransitivity` reaches `composed_half`
  through `transitivityIso`, `transitivityEquiv` and `forward`, all private
  declarations of `RefinementInductionTransitivityProof`. `composed_half`
  uses `refinedOuterHalfModulus_projection`, which uses
  `refinedOuterModulus_projection`. Its proof reaches
  `determinantNorm_refinedUnipotent` by the chain
  `leviModulus_refinedUnipotent` → `refinedUnipotent_le_ker_leviModulus`
  → `refinedUnipotent_le_normOneLevi` → `determinantNorm_refinedUnipotent`.
- `refinedInductionTensor` applies
  `RefinedInductionTensor.comparison_of_pointwiseMap_bijective` to
  `RefinedInductionTensor.pointwiseMap_bijective`. The latter obtains
  compact parabolic quotients from
  `Langlands.AllFieldBZ.Parabolic.parabolicQuotientCompact` and uses
  `Langlands.Induction.finiteProductTensorMap_bijective`. Compactness uses
  the integral representatives supplied by
  `Langlands.GeneralLinear.Iwasawa.exists_mul_upperTriangular`.

### Exact classes and rank zero

`multiplication_assoc` reaches `Langlands.SmoothRep.irreducibleGrothendieckStatement`
through `assoc_on_objects` and `inclusion_zero_eq_smul`. This result proves
that `realizeIrreducibles` is bijective. It reaches `factorMap`,
`classFactors_isExactAdditive` and `compositionFactors_shortExact` in
`Langlands.SmoothRep.IrreducibleGrothendieckProof` in that order. The last of
these uses `HasJordanHolderMultiplicity.unique`, which reaches
`jordanHolderSeriesComparison` by `jordanHolderMultiplicityIndependence`.
It also uses `jordanHolderShortExactAdditivity`, which reaches
`actualQuotientSeriesLift` by `jordanHolderFiltrationAdditivity` and
`jordanHolderSeriesTransport` by the multiplicity transport theorems
`equivJordanHolderMultiplicityTransport` and
`equivCompositionSeriesMultiplicityTransport`.

`multiplication_unit_left` and `multiplication_unit_right` use the private
`leftUnit_object` and `rightUnit_object` respectively. These use
`binaryLeftZeroTensorEquiv` and `binaryRightZeroTensorEquiv` from the
all-field `BinaryProduct` module, with `Langlands.BinaryTensor.secondFactorUnitEquiv`
and `Langlands.BinaryTensor.firstFactorUnitEquiv` to remove the trivial line.
The `unit` definition uses `unitObject_hasFiniteLength`, which applies
`Langlands.Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_finiteDimensional`
to that line.

### Declarations in classification modules

The declarations reached in modules under `Langlands.Representation.Classification`
are the three in this table.

| Declaration | Kind | Module | Reached from |
| --- | --- | --- | --- |
| `Langlands.Classification.BinaryProductBridge.binary_eq_twoBlocks` | theorem | `TwoSupercuspidalBinaryProductBridge` | `pairProductEquiv` |
| `Langlands.Classification.twoBlockFactors` | definition | `TwoSupercuspidalProductStructureStatement` | `pairProductEquiv`, `pairFamilyEquiv`, `regroupLeftPair`, `regroupRightPair` |
| `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` | theorem | `SupercuspidalTwist` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantNorm_refinedUnipotent` in `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCharacter` |

The first says that the shape `BlockShape.binary a c` equals
`Shahidi.twoBlocks a c` by checking cases on `Fin 2`. The second is
the family `(A₀, A₁)` on the two blocks of `Shahidi.twoBlocks k l`. The third
gives determinant one for a matrix in a standard block unipotent radical,
as used by the modulus calculation in ordered regrouping.

## Provenance

The theorem is an internal consequence of results in the Library and adds no
external assertion. The paired statement Markdown cites Zelevinsky 1980
§1.7(a), (c), printed p. 173. There associativity is derived from
transitivity of induction (§1.1(c)) and its tensor-coordinate form (§1.5),
which `orderedProductRegrouping` supplies here, and the unit is the trivial
representation of \(G_0 = \{e\}\). Zelevinsky leaves a rank-zero factor in a
triple product implicit; here it is reduced to integral multiples of the
unit class. [Statement and source citation](LocalFieldGradedAssociativeUnitStatement.md)
