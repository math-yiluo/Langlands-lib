# Conditional assembly of the affine extension step

`Langlands.AlgebraicGeometry.Picard.affineOpenImmersionLineBundleExtension_of_ideals.{u}`
is a proof-producing definition of `AffineOpenImmersionLineBundleExtensionStatement.{u}` from the two explicit
hypotheses `QuasiAffineLineBundleIdealEmbeddingStatement.{u}` and
`OpenImmersionInvertibleIdealExtensionStatement.{u}`. This is an internal derived
helper in arbitrary universe `u`. It proves neither input proposition and is not
an unconditional proof of affine or general line-bundle extension.

The proof introduces the affine target `X`, its locally Noetherian instance, the
open immersion `j : Y ⟶ X`, the complement-only factoriality assumption, and the
actual line bundle `D` on `Y`. It obtains local Noetherianity of `Y` from the open
immersion. The ring of global functions of the affine target is Noetherian by
`IsLocallyNoetherian.component_noetherian`; `noetherianSpace_of_isAffine` then
gives a Noetherian underlying space for `X`. The open embedding induces a
Noetherian topology on `Y`, while `Scheme.IsQuasiAffine.of_isImmersion j` gives
its quasi-affineness. In particular, the source satisfies precisely the premises
of the first input proposition, with no extra hypothesis on the original data.

The first input supplies an actual module-sheaf monomorphism from `D.obj` into
the structure module of `Y`. After installing that monomorphism instance, the
second input extends it and provides an actual line bundle `E` on `X` together
with an actual pullback isomorphism to `D.obj`. The definition keeps `E` and this
isomorphism as the required witness. The stronger monomorphism and commuting
inclusion equation supplied by the second input are not needed by the affine
statement.

The provenance is the formal composition of the three published propositions
named above and the cited Mathlib instance lemmas used in the Lean proof. No
external geometric construction or theorem is added or assumed beyond the two
explicit input propositions. This helper adds no integrality, connectedness,
separatedness, projectivity, reducedness, or bundle restriction to the affine
target statement and uses none of the prohibited downstream valuative extension
conclusions. It leaves the input propositions unchanged.
