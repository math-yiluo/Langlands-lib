# Relative dimension of the chosen dual over an algebraically closed field

Author: Worker 3643.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionProof`
proves the published proposition `AlgClosedFieldDualSchemeRelativeDimensionStatement`: for
every algebraically closed field `K` (in an arbitrary universe `u`), every abelian scheme `A`
over `Spec K` with `hA : HasDualScheme A`, and every `g : ℕ` with `A.HasRelativeDimension g`,
the structure morphism of the chosen dual `dualScheme A hA ⟶ Spec K` is
`SmoothOfRelativeDimension g`. This is the dimension part of Theorem (6.18) of Edixhoven, van
der Geer and Moonen, *Abelian Varieties*, for the Library's chosen dual, as recorded in the
statement's Markdown. The proof below is internal and composes published Library theorems
with the helper modules `Picard.DualSchemeSubalgebraFactorization` and
`SubalgebraFactorizationFiniteType` submitted with it.

Compared with the published conditional reduction
`algClosedFieldDualSchemeRelativeDimension_of_inputs` (module
`Picard.AlgClosedFieldDualSchemeRelativeDimensionReduction`), the hypothesis
`RelativeDualSchemeFinitePresentationStatement` (local finite presentation of chosen duals
over every quasi-separated base, which has no published proof) is not used: over `Spec K` it
is replaced by the proved `dualScheme_locallyOfFinitePresentation` and
`dualScheme_locallyOfFiniteType` of module `Picard.DualSchemeSubalgebraFactorization`, which
hold over noetherian affine (respectively affine) bases. The remaining two inputs of that
reduction are now published theorems.

## `algClosedFieldDualOriginDimensionLowerBound_of_mumford_ample`

Hypotheses: the Library propositions `MumfordBundlePicardZeroStatement` and
`GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`. For `K` algebraically closed,
an abelian scheme `A` of relative dimension `g` over `Spec K` and `hA : HasDualScheme A`, the
local ring of the chosen dual at its rational origin has Krull dimension at least `g`.

The proof is that of the published `algClosedFieldDualOriginDimensionLowerBound_of`, with the
instance `LocallyOfFiniteType (dualScheme A hA).hom` supplied by
`dualScheme_locallyOfFiniteType`: an ample `L` from the ample-existence hypothesis has
finitely many rational translation stabilizers (`algClosedFieldAmpleTranslationStabilizerFinite`),
so the Mumford classifier `A → A^∨` of `L` is quasi-finite at the unit
(`quasiFiniteAt_dualClassifier`); the stalk dimension comparison `quasiFiniteAtStalkDimension`
and the smooth stalk dimension `fieldSmoothClosedPointStalkDimension` give the bound.

## `algClosedFieldDualSchemeRelativeDimension_of_mumford_ample`

The target proposition, from the same two hypotheses. The proof is that of the published
`algClosedFieldDualSchemeRelativeDimension_of`, with local finite presentation from
`dualScheme_locallyOfFinitePresentation`, the tangent identification `dualSchemeTangentH1`,
the bound `dim H¹(A, 𝒪_A) ≤ g` from `fieldStructureSheafH1DimensionBound`, and the lower
bound above. The origin stalk is regular of dimension `g`
(`fieldPointTangentLocalRegularity`). Every closed point is a group translate of the origin
(`GrpObj.exists_iso_apply_closedPoint`), so all closed stalks are reduced of dimension `g`.
With the Jacobson property this gives reducedness, smoothness
(`closedPointHomogeneousSmooth`) and relative dimension `g`
(`smoothOfRelativeDimension_of_ringKrullDim_stalk`).

## `algClosedFieldDualSchemeRelativeDimension`

The unconditional theorem, with type exactly
`AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}`. It applies
`algClosedFieldDualSchemeRelativeDimension_of_mumford_ample` to the two published theorems
`mumfordBundlePicardZero` (module `Picard.MumfordBundlePicardZeroProof`) and
`GroupScheme.algebraicallyClosedFieldAmpleExistence` (module
`AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof`). No hypothesis is added to the
statement's binders.

The import closure contains neither `AlgClosedFieldAmpleMumfordEulerSquareStatement` nor
`AlgClosedFieldMumfordDualEulerStatement`, nor any module downstream of them.
