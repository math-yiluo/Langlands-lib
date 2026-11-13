# Inverse-image comparisons and structural pullback for Deligne's sheaves

This module supplies derived sheaf infrastructure for the four actual objects
`eta,T,u,r` in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976),
Section 2 A, printed p.109 (PDF p.3), final paragraph, continuing on printed
p.110 (PDF p.4). The source's Proposition 2.4, printed p.110, also identifies
base change of the four objects associated to a special formal module with
inverse image. The present module constructs comparisons needed to formulate
such base change; it does not prove Proposition 2.4.

All declarations lie in `Langlands.DeligneFormalSpace`. Coefficient rings,
spaces and schemes are in one universe. The coefficient constructions require
commutative rings `O` and `R`; rationalization uses an `O`-algebra field `F`.
No fraction-field, valuation or nilpotence hypothesis is used for these
comparisons. The constructions apply in particular to the actual spectra of
Nilp algebras used by the existing four-data objects.

## Coefficients and inverse image

For a ring homomorphism `rho : O -> R`, `coefficientRestriction` is the actual
sectionwise restriction of scalar modules on sheaves. `coefficientExtension`
is sectionwise tensor extension followed by sheafification. The
`coefficientExtensionAdjunction` lifts the module tensor/restriction
adjunction through the actual sheafification adjunction.

`coefficientCoextension` is sectionwise module coextension on sheaves. It is
well-defined because that right adjoint preserves limits. Restricting the
presheaf restriction/coextension adjunction along the fully faithful sheaf
inclusions gives `coefficientRestrictionAdjunction`.

For an actual continuous map `f : X -> Y`,
`inverseImageExtensionIso` and `inverseImageRestrictionIso` are natural
isomorphisms

- `f^(-1)(R tensor_O M) ~= R tensor_O f^(-1)M`, with sheafification;
- `f^(-1)(Res M) ~= Res(f^(-1)M)`.

The proof composes the relevant coefficient adjunction with the actual
inverse-image/direct-image adjunction on each side. The two right adjoints
are definitionally equal: sectionwise coextension or restriction commutes
with precomposition by the map of open sets. Uniqueness of left adjoints
therefore supplies the displayed natural isomorphisms.

`topOpenIsTerminal` constructs the terminal object given by the top open.
`inverseImageConstantIso` applies the same uniqueness argument to the
constant-sheaf/global-sections adjunction. The inverse image of the top open
is definitionally the top open, so this gives a natural isomorphism from
inverse image of the actual constant `O`-module sheaf to the same constant
sheaf on `X`. It applies to the rank `d` free module used in the frame.

`coefficientExtensionRationalIso` is the identity comparison with the
previously defined `rationalSheafFunctor`: both are tensor extension followed
by the same sheafification. `inverseImageRationalIso` is its actual
inverse-image comparison. `rationalUnit_eq_adjunctionUnit` identifies the
existing map `m |-> 1 tensor m`, followed by sheafification, with the unit of
`coefficientExtensionAdjunction`. This follows from the sheaf adjunction's
explicit unit formula. `inverseImageRationalIso_naturality` records the
commuting square for every actual integral sheaf map, in particular for the
existing integral Pi operator.

## Structural scalars and the map u

For a scheme map `f : S' -> S` and `phi : O -> Gamma(S,top)`,
`pulledGlobalScalar` is the composite with the actual global-section map
`f.appTop`. The scalar identity `structuralScalar_pushforward` follows by
evaluating naturality of the scheme's structure-sheaf morphism on `phi(a)`.
It identifies the two local structural scalar actions on an inverse-image
open set.

`structuralPushforwardIso` compares structural-module pushforward followed
by forgetting scalars to `O`, with forgetting to `O` on `S'` followed by
ordinary sheaf pushforward. It is the identity on each underlying section.
The scalar identity just proved establishes its `O`-linearity; restriction
maps and module morphisms give its two naturality conditions.

`structuralPullbackUnit` applies the existing scalar-forgetting functor to
the unit of the actual structural-module pullback/pushforward adjunction,
then uses `structuralPushforwardIso`. Transposing this map under the ordinary
sheaf inverse-image/direct-image adjunction constructs the natural map
`structuralPullbackComparison`:

`f^(-1)(underlying_O T) -> underlying_O(f^* T)`.

`structuralPullbackComparison_unit` states its defining adjunction-unit
equation. This comparison is a map; no isomorphism is asserted. Structural
pullback extends scalars along the structure-sheaf morphism.

For existing `D : SheafPreDatum d pi F phi`, with positive `d`,
`SheafPreDatum.inverseImageU` applies ordinary inverse image to the same
actual total `D.u`, then composes with `structuralPullbackComparison` on
`D.tangent.graded.module`. `inverseImageUComponent` makes the same construction
on the actual homogeneous restrictions of `u`. The theorem
`inverseImageU_pi` combines functoriality with `D.uPi` and naturality of the
structural comparison. `inverseImageUComponent_inclusion` uses the original
homogeneous inclusion equation and that naturality to show that these are
still restrictions of one total map.

## Scope

These are concrete natural comparisons and maps, with their stated equations.
The source of `inverseImageU` is inverse image of the underlying integral
lattice sheaf; this module does not assemble a new graded flat lattice,
framed lattice or four-data object. Inverse-image preservation of the
internal grading and stalk flatness, structural line-sheaf pullback,
local generation, admissibility transport, functorial Nilp isomorphism
classes, and the normalized projective-linear action remain later work.
No representability or existence result is supplied, and the existing
stalkwise determinant-comparison qualification is retained.
