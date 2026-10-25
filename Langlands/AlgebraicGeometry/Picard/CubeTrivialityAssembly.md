# Actual cube trivialization from classification and rigidity

`Langlands.AlgebraicGeometry.Picard.cubeTrivializationOfUniversalFamily`
constructs an actual module-sheaf isomorphism from a line bundle on
`(X ⨯ (Y ⨯ Z)).left` to the structure sheaf. It works in every universe
over an arbitrary base scheme `S`, with three actual pointed objects
`X`, `Y`, and `Z` in `Over S`.

The inputs are an actual universal relative rigidified line bundle `U`
for `X`, a proof of its existing `RigidifiedLineBundle.IsUniversal`
predicate, an explicit two-axis rigidity property for morphisms
`Y ⨯ Z ⟶ P`, and ordinary module-sheaf trivializations along the three
published `CubeFace` morphisms. The rigidity property uses the parameter
section classifying the trivial family and the actual axes fixing `y₀`
and `z₀`. No compatibility is required among the three supplied ordinary
face trivializations.

The implementation first applies `CubeRelativeTransport.cubeRigidified`:
transport along `relativeSpaceProdIso` and the first-face trivialization
give a relative rigidified family `M` over `Y ⨯ Z`. The second- and
third-face adapters give ordinary carrier trivializations of its
restrictions over `Z` and `Y`. Each induced relative section is a section
of `relativeProjection`, by `relativeSection_projection`.
Consequently `RigidifiedLineBundle.trivialIsoOfCarrierIso` adjusts each
ordinary restriction trivialization to respect its actual rigidification.
This is the step that removes the need for compatibility assumptions
on the original face trivializations.

`RigidifiedLineBundle.trivialIsoOfTwoRestrictions` then applies the
supplied rigidity property to the classifier of `M`, identifies it with
the classifier of the trivial family, and recovers an actual rigidified
isomorphism. Applying the existing forgetful functors yields an ordinary
module-sheaf isomorphism on the relative space.
`CubeRelativeTransport.cubeRecoverTrivialization` transports this back
to the original cube module, which is the exact output of the
construction.

This is internal categorical assembly from the three imported modules;
it introduces no original-source geometric assertion. Those modules
provide the product and pullback comparisons, adjustment to a chosen
rigidification, and classification by actual compatible isomorphisms.
All are used through their existing interfaces, with no change to the
cube statement or its import closure.

The universal family and parameter rigidity are explicit inputs.
The construction proves neither their geometric existence nor
`FieldCubeTrivialityStatement`. In the intended field application,
the separate full rigidified Picard representability and two-axis
rigidity theorems must supply these inputs. Their proposition
definitions alone do not do so.
