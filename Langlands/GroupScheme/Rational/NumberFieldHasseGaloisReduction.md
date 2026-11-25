# Reduction of the number-field Hasse principle to finite Galois covers

This internal reduction preserves the published
`NumberFieldHassePrincipleStatement` unchanged. It does not prove its arithmetic
content.

`Cocycle.LocallyCohomologous ξ ζ` is defined for an arbitrary cover `U` over
a number field `F`. It says that at every place of `F` the two pullback
cocycles are cohomologous on the pullback cover. Both the cover and its projection
to `U` are the pullback and adjunction counit appearing in the published target.
The cohomology relation is the cochain-twist relation of `CocycleCohomology`.

`NumberFieldGaloisHassePrincipleStatement.{u}` states the same implication as the
published target, for the same three group classes, with the finite separable
cover replaced by a finite Galois field extension. It quantifies over every number
field and every finite Galois extension in `Type u`, and uses all places and their
actual completions. This is a `Prop`-valued definition, not an axiom.

`numberFieldGaloisHassePrinciple_iff` proves that this restriction is equivalent
to the published target. The forward direction embeds a finite separable extension
`L/F` into a finite Galois extension `E/F` using the published
`exists_finite_galois_algHom`. The resulting morphism `Spec E → Spec L` is fpqc
by `fieldExtension_fpqc`. Both cocycles are refined along that morphism.
Local cohomology is preserved by refinement, so the Galois hypothesis gives
cohomology of the refined cocycles. `cohomologous_refine_iff` descends the
witnessing cochain to `Spec L`. The reverse direction specializes the original
statement to a Galois extension, which is separable.

The supporting lemma `baseChange_pullback_refine_toFun` proves that refining a
cover commutes on all cocycle values with pulling the cover back along an
arbitrary base morphism. Its proof applies `baseChangePointsEquiv` and the
naturality of the pullback adjunction's counit. `LocallyCohomologous.refine`
then restricts each local cochain along the pulled-back refinement and uses this
compatibility.

Provenance is internal. This is a reformulation and a formal reduction of the
published number-field target, using the published normal-closure and fpqc
reflection constructions. It introduces no new source-dependent arithmetic
assertion, no extra hypotheses and no restriction on the group classes or places.
