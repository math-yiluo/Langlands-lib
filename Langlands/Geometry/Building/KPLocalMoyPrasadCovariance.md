# Covariance reductions for the K-level Moy–Prasad groups

This internal helper adapts the generator argument of
`MoyPrasadNormalizerCovariance` to the groups defined in
`KPLocalMoyPrasadGroups`. It concerns clause 2 of
`LocalMoyPrasadGroupPropertiesStatement`, as stated and sourced in
`KPLocalMoyPrasadGroupProperties`.

`BuildingData.RootFiltrationConjugationBound B hZ` is a `Prop`-valued
interface for the root-generator input: for every apartment point `x`,
depth `r ≥ 0`, roots `a,b`, and elements `u ∈ U_{a,x,0}` and
`v ∈ U_{b,x,r}`, the conjugate `u v u⁻¹` belongs to `G(K)_{x,r}`.
It names the explicit hypothesis of
`localMoyPrasadNormality_of_root_conjugation`. The definition supplies no
proof of that hypothesis. This internal interface packages the generator
bound used by the reduction below, including its opposite-root cases.

`sharpFixer_le_moyPrasad_zero` follows from
`KPApartmentData.sharpFiltration_zero` and the defining inclusion of the sharp
filtration. `conj_mem_moyPrasad_normalizer` uses an explicit hypothesis that the
torus image is stable under normalizer conjugation. On root generators it uses
`KPApartmentData.conj_mem_filtration` and
`weylAction_mapsTo_relativeRoots`. Applying this inclusion to the inverse
normalizer element proves `moyPrasad_map_conj_normalizer`.

`localMoyPrasadEquivariance_of_normality` additionally assumes clause 1,
`LocalMoyPrasadNormality`. Equality of building representatives, via
`ApartmentQuotient.mk_eq_mk_iff`, supplies a normalizer element `n` with
`n • x = x'` and `g⁻¹ n` in the sharp fixer of `x`. Its inverse normalizes
`G(K)_{x,r}` by clause 1. The identity `g = n (g⁻¹ n)⁻¹` and normalizer covariance
then give the required conjugation equality.

These are conditional reduction lemmas, not a proof of the full group properties
statement. A final proof must supply normality and normalizer stability without
adding hypotheses to that statement.


The following additional reductions have been implemented and compiled.
`block_subset_moyPrasad` puts both the ordinary root factor and the actual
doubled-root factor in the same-depth group; an absent doubled root contributes
the identity. `conjugate_root_mem_moyPrasad_of_nonopposite` applies V3 through
`KPApartmentData.filtration_commutator_le`; the depths of its output roots are
at least the positive input depth because their second integer coefficients
are at least one. Multiplying the commutator by the original root element
recovers the conjugate.

`conjugate_image_mem_moyPrasad` uses the root-compatibility clause of S1,
explicitly as a hypothesis. `sharpFixer_le_normalizer_moyPrasad_of_root_conjugation`
combines this with an explicitly supplied root-conjugation bound and the
root-generator definition of the sharp fixer.

The existing `image_le_normalizer_filtration`, imported from
[`KPLocalMoyPrasadBlockExchange`](KPLocalMoyPrasadBlockExchange.md), is unconditional:
the torus filtration
lies in the character-valuation kernel, `valuation_isEquiv` compares the
integer and spectral kernels, and V6 makes the resulting normalizer element
fix the apartment point. `torusImage_normalizes_moyPrasad` combines this with
commutativity of the centralizer torus. Finally,
`localMoyPrasadNormality_of_root_conjugation` supplies all torus-generator
cases and reduces full normality to root conjugation and root compatibility.
The opposite-root cases are separate inputs to this helper; none of these lemmas asserts them or the full S2 statement.
