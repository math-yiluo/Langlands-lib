# Smoothness of the supplied local model with reductive fibres

This internal prerequisite proves
`IntegralModel.isSmooth_of_reductive_localField` for every universe `u`,
nonarchimedean local field `F`, supplied connected reductive group `G`, and
actual supplied model `M : IntegralModel 𝒪[F] F G` whose full special-fibre
pullback is connected reductive.

Connected reductivity gives smoothness of `G`. The supplied `M.genericIso`
transfers it to the actual generic pullback. Connected reductivity of the
full special fibre gives smoothness of that actual pullback along the
canonical residue quotient. The integer ring is a DVR. Flatness and local
finite type already belong to `M`, so the general DVR smooth-fibre criterion
proves smoothness of the original structural morphism `M.group.X.hom`.
This is exactly the existing predicate `M.IsSmooth`.

The coefficient maps are the actual canonical inclusion `𝒪[F] → F` and
quotient `𝒪[F] → 𝓀[F]`. The supplied generic isomorphism is retained.
The proof imposes no characteristic, splitness, rank, building or additional
smoothness premise. It proves a smoothness prerequisite and makes no
maximal-compactness assertion. The argument is derived from the existing
model and reductivity interfaces and the companion DVR fibre comparison;
it uses no additional external source.
