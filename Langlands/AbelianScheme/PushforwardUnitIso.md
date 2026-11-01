# Structure-module comparisons for abelian-scheme families

For every `A : AbelianScheme S`, this internal adapter provides actual
isomorphisms from the structure module on the base to the direct image
of the structure module on each of the following actual families:

- `A.X.hom : A.X.left → S`;
- `((relativeProjection A.X.hom).app T) : T ×_S A → T`, for every
  `T : Over S`;
- `(mumfordProduct A).hom : A ×_S A → S`, with exactly the target's
  parameter-first self-product;
- `((relativeProjection (mumfordProduct A).hom).app T) :
  T ×_S (A ×_S A) → T`, for every `T : Over S`.

The corresponding definitions are `pushforwardUnitIso`,
`relativePushforwardUnitIso`, `mumfordPushforwardUnitIso` and
`mumfordRelativePushforwardUnitIso` in namespace
`Langlands.AbelianScheme`. In each case the `_hom` lemma states that
the forward morphism is the published
`Langlands.Scheme.Modules.unitToPushforwardUnit` for that exact
projection. Thus these definitions retain the canonical comparison,
and concern actual module sheaves.

They apply the generic adapter
`Langlands.Scheme.Modules.pushforwardUnitIso`. An abelian scheme is
smooth, proper and geometrically connected by its Library definition.
These properties persist under every base change. The structure map
of the self-product is the composite of its first projection and
`A.X.hom`. Smoothness and properness persist under composition.
Mathlib's `GeometricallyConnected.comp` gives geometric connectedness;
smoothness supplies the needed universal openness. The same properties
then hold on each displayed base change.

The base scheme and test scheme are arbitrary and the universe `u` is
unrestricted. Applying the definitions to
`(AbelianScheme.baseChange f).obj A` also covers the Library's actual
`A ×_S T → T` and its self-product, including any chosen fraction-field
base change in the valuation-ring extension target.

This is internal derived infrastructure, using the published
`AbelianScheme.Basic`, `Picard.MumfordBundle` and
`Modules.PushforwardUnitIso` interfaces. It does not construct a
correspondence space or prove extension over a valuation ring.
