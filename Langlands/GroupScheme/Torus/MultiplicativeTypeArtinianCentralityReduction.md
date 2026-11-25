# Fibrewise centrality over Artinian bases, from infinitesimal centrality

This internal reduction uses
`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalCentralityStatement` as
an explicit premise. That published statement is proved as
`multiplicativeTypeInfinitesimalCentrality` in
[`MultiplicativeTypeInfinitesimalCentralityProof`](MultiplicativeTypeInfinitesimalCentralityProof.md). The reduction supplies the Artinian detection argument toward SGA
3, Exposé IX, Théorème 5.6(b).

`isCentral_field_baseChange` factors a map from the spectrum of a field through
the residue field of its image point, using Mathlib's `SpecToEquivOfField`.
Centrality of the residue fibre then persists under the further field base
change and the canonical comparison of successive pullbacks.

`ker_specMap_appTop` identifies the kernel on global sections of a spectrum map
with the image of the original ring kernel under the canonical
spectrum/global-sections isomorphism. This follows by the naturality of that
isomorphism and injectivity of its inverse. `locallyNilpotent_specMap` uses this
identification and preservation of nilpotence under ideal image to give the
locally nilpotent ideal-sheaf condition, choosing the whole affine spectrum.

`isCentral_artinian_baseChange` assumes a multiplicative-type source `H`,
an ambient group `G` locally of finite presentation over `S`, and centrality
on every residue fibre. For any local Artinian ring `A` and map `Spec A → S`,
the maximal ideal of `A` is nilpotent. Thus the actual residue quotient map
has nilpotent kernel and its spectrum satisfies the required infinitesimal
condition. The preceding field-valued result gives centrality after that
quotient. The explicit infinitesimal-centrality premise lifts it over `A`.
The source remains of multiplicative type and the ambient structure map remains
locally of finite presentation under this base change.

`isCentral_of_fibres` assumes in addition that `H ×_S G` is locally noetherian.
It applies `ArtinianCentrality.isCentral_of_artinian_baseChange_general` to
the Artinian centrality just proved. This theorem does not assume affineness,
separatedness, quasi-compactness, connected fibres, or a monomorphism.

`isCentral_of_fibres_of_locallyNoetherian` instead assumes that `S` is locally
noetherian and `H → S` is locally of finite type. The local finite presentation
of `G → S` makes `G` locally noetherian. The product over `G` is locally of
finite type, so it too is locally noetherian and the preceding criterion
applies. The local finite type of `H → S` is an explicit hypothesis here.

For a monomorphic `i`, `commGroupSchemeOfFibrewiseCentrality` bundles the same
group scheme `H` and its operations as commutative, using the proved
conditional centrality. Its `toGrp` equality is reflexive.

Every result retains the infinitesimal-centrality premise where it is used.
The module proves neither that premise nor approximation to an arbitrary
non-noetherian base, and does not claim the full fibrewise-centrality statement.
Its proof is derived from the cited Library interfaces and Mathlib's actual
residue quotient, nilpotence, and noetherian base-change constructions.
