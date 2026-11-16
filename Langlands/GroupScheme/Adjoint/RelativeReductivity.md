# Reductivity of supplied affine full-centre quotients

Worker 795.

`RelativeRoot.IsFppfQuotient.isReductive_target` says that a supplied affine
full-centre fppf quotient `q : G ⟶ Q` of a reductive group scheme over any
scheme has reductive target. The only additional target hypothesis is
`IsAffineHom Q.X.hom`. The full scheme-theoretic centre is retained, including
any nonsmooth or nonreduced part. There is no smoothness assumption on the
kernel and no affine, finite-type or Noetherian assumption on the base.

`isRelativeAdjointQuotient` packages the result with the source reductivity
and the supplied quotient to obtain `IsRelativeAdjointQuotient q`. Its inner
action and all base-change and field comparisons are then available from the
imported relative quotient API.

## Implemented proof and provenance

This is internal infrastructure derived from published Library results.
It constructs no quotient and asserts no new external-source theorem.

The source structure morphism is smooth, hence flat and locally of finite
presentation. Its factorization through the flat, surjective, locally
finitely presented quotient map descends flatness of `Q → S` by
`AlgebraicSpace.flat_of_surjective_flat_comp`, and local finite presentation
by `locallyOfFinitePresentation_of_surjective_flat_comp`.

At every field-valued point of the base, the source is connected reductive
by `IsReductive.isConnectedReductive_baseChange`. The pulled-back quotient
is still a quotient by the full centre by `baseChange_center`; its target is
affine and locally of finite type. The published `centerQuotientReductive`
therefore makes every such target connected reductive.

In particular, the actual residue-field fibres are smooth. Mathlib's
`Smooth.of_smooth_fiberToSpecResidueField`, together with the descended
flatness and local finite presentation, proves smoothness of `Q → S`.
At the geometric points, the connected reductive conclusion supplies the
pseudo-reductive geometric fibres required by `IsReductive`. This proof
uses neither smooth-kernel descent nor a choice of integral quotient.
