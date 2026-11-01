# Universality of smooth families on tests over an open of the base

Helper module for the proof of
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement`.
Everything lives in the namespace
`Langlands.AbelianScheme.SmoothFamilyOpenCover`. It proves no published
statement by itself; its results are used by
[`SmoothFamilyOpenCoverGluing`](SmoothFamilyOpenCoverGluing.md) and
[`SmoothFamilyAbelianRepresentabilityOfOpenCoverProof`](SmoothFamilyAbelianRepresentabilityOfOpenCoverProof.md).
Throughout, `A` is an abelian scheme over an arbitrary scheme `S`.

## Notation and class lemmas

The scoped notations `cp[A]`, `cm[A]`, `cl[A]` and `rp[A]` abbreviate the
published `RigidifiedLineBundle.classesPullback`, `classifyingMap`, `classOf`
and `relativePullback` for the unit section of `A`. Composition reuses
`Langlands.AbelianScheme.classesPullback_comp` from `MumfordParameterAxes`.
The lemmas `cp_id`, `cm_comp`, `cm_id`, `cl_pullback`, `cm_pullback` and
`cl_eq_of_iso` record the other pullback laws; `cp_id` uses
`relativePullbackId` with `RigidifiedModule.pullbackCoherence`.
`isAlgTrivClass_pullback` is the class-level form of the published
`smoothFamilyPullback`; `atPullback` and `atClass` package pulled-back classes
and classes of families as elements of
`AlgebraicallyTrivialClassesViaSmoothFamily`.

## Universality over an open

`IsUniversalOn A V L` says that `L` uniquely classifies every smooth-family
algebraically trivial class on every quasi-separated test `T` whose structure
map lands in the open `V` of `S`. It is an internal auxiliary predicate.

- `existsUnique_of_iso` transports unique classification along an
  isomorphism of tests.
- `eq_of_cm_eq` says that two maps from such a test into a family universal
  over `V` agree if they classify the same algebraically trivial class.
- `isUniversalOn_of_isPullback`: if `L` on `X` is universal over `W`,
  `V ≤ W`, and `Y` over `S` sits in an actual pullback square of `X.hom`
  along `V.ι` through `f : Y ⟶ X`, then the actual rigidified pullback of `L`
  along `f` is universal over `V`. A test landing in `V` is classified by
  some `h` into `X`; the square lifts `h` uniquely to `Y`, using
  `IsOpenImmersion.lift` to factor the test through `V`.
- `isIso_of_isUniversalOn` is the Yoneda argument: two smooth-family
  algebraically trivial families universal over `V`, on quasi-separated
  parameters landing in `V`, have isomorphic parameters, and any map
  classifying one family by the other is an isomorphism.

## Translation of local universal families

For an open immersion `b : U ⟶ S`, `isUniversalOn_familyBaseChangeInverse`
turns a family universal for `(baseChange b).obj A` on quasi-separated tests
over `U` into the family `(familyBaseChangeInverse b A P).obj L` for `A`,
universal over `b.opensRange`. A test landing in the range of `b` is
identified, by `IsOpenImmersion.lift`, with the image under `Over.map b` of a
test over `U`. The published equivalence `familyBaseChangeCounitIso`,
`classesBaseChange_pullback`, `classesBaseChange_injective` and
`isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff` translate
classification in both directions (`classesBaseChange_classifyingMap`,
`isAlgebraicallyTrivial_familyBaseChangeInverse`). Maps between images under
`Over.map b` descend by `overMapPreimage`, since `b` is a monomorphism.

## Geometric fibres

- `isIso_fibreComparison_left`: the underlying scheme map of the published
  `GroupScheme.fibreComparison A.toGrp h s` is an isomorphism. Both iterated
  pullbacks are pullbacks of `A.X.hom` along `s ≫ T.hom` by pasting
  (`IsPullback.paste_horiz`), and `fibreComparison_fst` and
  `fibreComparison_snd` identify the comparison with
  `IsPullback.isoIsPullback`.
- `isAlgebraicallyTrivial_fibre_of_relativePullback` is the converse
  direction of the argument of `smoothFamilyPullback` at one geometric point:
  the smooth-family witness for the fibre of the pulled-back family is pulled
  back along the inverse of the fibre comparison
  (`isAlgebraicallyTrivialViaSmoothFamily_pullback_hom`) and identified with
  the fibre of the original family through `fibreComparison_lineBundleIso`,
  `LineBundle.pullbackComp` and `LineBundle.pullbackId`.
- `isAlgebraicallyTrivialFamily_of_openCover`: a rigidified family whose
  actual pullbacks to all members of an open cover of its parameter satisfy
  the smooth-family condition satisfies it itself. A geometric point
  `Spec K ⟶ U.left` has a one-point source, so it factors through a member
  of the cover by `IsOpenImmersion.lift`.

## Provenance

These are internal derived lemmas about the published actual interfaces
(`RigidifiedClassPresheaf`, `SmoothFamilyAlgebraicTriviality`,
`FamilyBaseChangeEquivalence`, `SmoothFamilyPullbackProof`,
`SmoothFamilyUniversalBaseChangeProof`, `FibreComparison`,
`PicardZeroPullbackComparison`). No literature assertion is used beyond those
already recorded for the published inputs.
