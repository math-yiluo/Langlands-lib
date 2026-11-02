# Actual extensions with two trivial total-space axes

Worker 513 authored this internal specialization of the ordinary two-axis
normalization construction. It applies to an existing actual extension
along the canonical self-product base-change map. Combining it with the
published Noetherian valuation extension produces an extension whose two
total-space axes are trivial.

Fix a universe `u`, an abelian scheme `A / S`, and an arbitrary map
`b : T → S`. Let `B = A ×_S T` be the Library's actual base change, and
let `q = mumfordProductBaseChangeMap A b`. This is the actual canonical map
`B ×_T B → A ×_S A`, defined by the two carrier projections followed by
`π : B → A`. No replacement of the schemes or of `q` is made.

`TwoAxisTrivialExtensionData A b D` records four pieces of actual data:

- A Library line bundle `E` on `A ×_S A`.
- An ordinary module-sheaf isomorphism `(id,e_A)*E ≅ O_A`.
- An ordinary module-sheaf isomorphism `(e_A,id)*E ≅ O_A`.
- An actual module-sheaf isomorphism `q*E ≅ D`.

For an existing actual extension `q*E₀ ≅ D` and actual trivializations of
both axes of `D`, `twoAxisTrivialExtensionOfExtension` returns this data.
Its bundle is the ordinary normalized bundle of `E₀`. Its two total-space
trivializations are those supplied by ordinary normalization.

The auxiliary definition `twoAxisNormalizedBaseChangeRestrictionIso`
supplies the last field. The canonical product map commutes with both
projections by the defining pullback identities. The actual base-change
unit commutes with the carrier projection by
`GroupScheme.identitySection_baseChange_fst`. The published cartesian
self-product lemmas then give the two axis squares. Applying
`LineBundle.twoAxisNormalizedBundleRestrictionIso` to these four squares
recovers `D` up to an actual isomorphism. The unconditional theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` supplies the
normalization construction's tensor-preservation input.

The definition `noetherianValuationRingTwoAxisNormalizedExtension` fixes a
commutative Noetherian valuation domain `R : Type u`, any specified fraction
field `K : Type u` with its given algebra structure, and an abelian scheme
over `Spec R`. Its input is an actual line bundle on the actual generic
self-product and the existence of ordinary trivializations on both generic
unit axes. The published `noetherianValuationRingSelfProductExtension`
first supplies an actual extension and its actual restriction isomorphism.
Classical choice selects the two generic axis trivializations. Applying
the general normalization construction supplies the displayed four-field
extension data. Fields are included in this result; no discrete,
completeness, henselianity, characteristic, ampleness or projectivity
hypothesis is added.

This is derived internal content, with no new literature assertion or
axiom. The first construction requires an existing extension. The second
requires Noetherianity. The returned restriction isomorphism need not
respect the two generic trivializations used as inputs. Consequently these
constructions do not assert extension of preselected compatible
rigidifications or surjectivity of the compatible-rigidified class
presheaf. They do not construct a correspondence representation or prove
the host extension theorem over arbitrary valuation domains.
