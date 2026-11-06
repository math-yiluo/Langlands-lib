# Integral-normalization compatibility with actual Harris pullback

This internal supporting unit proves that the existing pointed Harris pullback
preserves and reflects the additional integral Tate-image normalization of
original compatible frames and monodromy-fixed level orbits. It constructs the
restriction of the literal `levelDataBaseChange` to normalized representatives.
It does not prove
existence of normalized representatives or a representing scheme.

## Objects and hypotheses

All arithmetic carriers are universe zero. The data are the existing totally
real number field `E`, totally complex quadratic extension `F/E`, algebra `A`,
central simple unitary datum `D`, and normalized Harris signature charts `C`,
with the displayed rational scalar tower. The auxiliary star structure is
`auxiliaryStarRing D C`; the form is the unchanged `D.harrisHodgePELForm C`.

`P` is the existing `PolarizedFiniteLevel.Prerequisites` bundle of tensor,
Picard, and duality prerequisites. The construction also retains
`DualAbelianBaseChangeNaturalityStatement` and
`PolarizationBaseChangeStatement`, as required by the existing positive
polarized action pullback. The bases `S` and `T` are quasi-separated schemes,
`b : T ⟶ S` is any morphism, and `t : Spec Ω ⟶ T` is a field-valued point.
Neither algebraic closedness of `Ω` nor connectedness or local Noetherianity
of either base is required here.

`X` is the original `PositivePolarizedAction` on `S`. Its pullback dual input
`W : PositivePullbackDualData ... b X` is indexed by the actual scheme
`(AbelianScheme.baseChange b).obj X.actionObj.abelianScheme`. It supplies the
existing dual geometry, inverse Poincare bundle, evaluation, and dual-map
additivity data on that same scheme. The actual changed positive polarized
action is `framedPositiveActionBaseChange`, with its existing polarization,
action, positivity, and faithfulness proofs. The frame nonemptiness input is
an ambient adelic frame at `t ≫ b`; it is not an integral normalization premise.

The Weil transition prerequisite and rational profinite-integer/adele comparison
are unchanged. A compatible frame is the actual `Tate.WeilAdelicFrame` for the
original Harris form. `HarrisIntegralFrameCondition` is the predicate already
defined in `HarrisIntegralTateImages`: for every vector `v` in the original
finite-adelic scalar extension, membership in the constructed span of the
actual Harris integer lattice over integral finite adeles is equivalent to
`eta(v)` belonging to the image of the canonical rationalization of the full
integral Tate module. The predicate uses every positive torsion index through
`fun _ => True`.

The level results additionally retain finite cover-fibre hypotheses at `t`
and `t ≫ b`, the torsion finite-etale prerequisite, invertibility of every
positive integer on both bases, and finiteness and etaleness of their actual
roots-of-unity schemes. `K` is an original
`FiniteAdelicScalarExtensionLevel`, and its level elements are the original
monodromy-fixed right orbit classes. Normalization of a level means existence
of a normalized frame in that orbit. It does not mean that a frame itself is
fixed by monodromy.

## Full Tate-image comparison

The private helper `fullImage_baseChange_iff` proves, for the same actual
abelian scheme and any element `z` of its pulled-back rational Tate module,
that `z` is in the full integral rationalization image if and only if its image
under `Tate.rationalBaseChange` is in the corresponding source image at
`t ≫ b`.

In the forward direction the witness is its image under the actual integral
base-change equivalence. Compatibility with rationalization is definitional.
In the reverse direction, surjectivity of that integral equivalence lifts the
source integral witness. Injectivity of the rational equivalence then proves
that its rationalization equals `z`. No injectivity of the integral-to-rational
map is needed.

## Compatible frames

`harrisIntegralFrameCondition_baseChange` states that, for any source compatible
frame `eta`, the inverse of the existing `weilAdelicFrameBaseChange` is
normalized on the actual pulled-back polarized action exactly when `eta` is
normalized on `X`.

The direction of the original frame comparison is from pulled-back frames to
source frames. Its inverse evaluates as the inverse rational Tate equivalence.
Applying the private image equivalence at each vector and cancelling this
rational inverse gives the two implications. The source integral span does not
change under this operation, and the proof changes neither the form nor the
opposite right precomposition action.

## Original fixed levels and representatives

`harrisIntegralLevelCondition_baseChange` proves that the existing
`Tate.weilAdelicLevelBaseChange` preserves and reflects normalization at every
original scalar-extension level `K`. This map is a map of fixed orbit sets;
its underlying orbit is the inverse of
`weilAdelicFrameRightOrbitBaseChange`. The theorem does not assert that the
fixed-orbit map is surjective.

For preservation, transport a normalized source frame by the inverse frame
comparison. The frame theorem gives normalization, and the original inverse
orbit comparison computes its orbit as the pulled-back class. For reflection,
transport a normalized frame of the pulled-back class by the forward frame
comparison. The frame theorem, evaluated at that transported frame, gives
source normalization. Apply the forward orbit equivalence to the witness's
orbit equality and cancel its inverse to recover the source class. Because
the condition is existential on representatives, no containment of `K` in the
source lattice stabilizer is needed for this equivalence.

`harrisIntegralLevelCondition_levelDataBaseChange` specializes this result to
the existing `HarrisLevelData` at any original `HarrisLevel D`. It uses the same
`hodgeLevelFunctor D C`, source representative, and literal
`levelDataBaseChange`. The supplied dual-data function is indexed by source
positive polarized actions and their actual abelian-scheme pullbacks.
`level_nonempty_adelicFrame` obtains the ambient frame required for the
faithfulness proof from the source level orbit. The final result is then the
fixed-level theorem: the changed object and level are definitionally those of
the original representative pullback.

`harrisIntegralNormalizedLevelDataBaseChange` consumes this equivalence.
At each original level `U`, its source is the subtype of the existing
`HarrisLevelData` at `t ≫ b` whose fixed orbit satisfies
`HarrisIntegralLevelCondition`; its target is the analogous subtype at `t`.
It applies the literal `levelDataBaseChange` to the source representative.
The preservation direction of the proved equivalence supplies the target
normalization proof. Thus no normalization-preservation hypothesis is added
to the original pullback inputs.

`harrisIntegralNormalizedLevelDataBaseChange_val` is proved by reflexivity:
forgetting the normalization proof gives the original representative pullback
on the nose. This is a map of representative subtypes at a fixed level. It
does not assert surjectivity, descent through rational-isogeny classes, or
functorial coherence. No replacement orbit quotient or level category is
introduced.

## Provenance and remaining obligations

This is an internal consequence of the existing actual integral and rational
Tate base-change equivalences, their compatibility with rationalization, and
the original compatible-frame and fixed-orbit constructions. There is no
external existence theorem or new source assertion in this unit. Its only
integral-image and frame-normalization inputs are the two sides of the proved
equivalences.

These results provide base-change compatibility needed for an eventual natural
normalized-moduli comparison. They do not construct normalized models, reflect
rational isomorphisms to actual integral morphisms, identify an ordinary
moduli problem with the normalized CM presheaf, or prove representability,
admissibility, smoothness, or division-case projectivity. The exact
`DivisionCMRepresentabilityStatement` remains an open obligation.
