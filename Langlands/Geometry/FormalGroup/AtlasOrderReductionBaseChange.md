# Reduction and varying nilpotent coefficients with the full acting order

This is an internal specialization of `AtlasOrderBaseChangeAlongSquare` and
`AtlasOrderReduction` at the canonical quotient naturality square from
`ModuleReduction`. `AtlasReductionBaseChange` supplies the underlying ambient
comparison. No additional original-literature assertion is made.

## Inputs and actual formal comparison

Let `O` and `R` be commutative rings with `Algebra O R`, let `pi` be any element
of `R`, and let `f : A -> B` be a morphism of actual objects of `Nilp R pi`.
Let `D` be any ring with a central `O`-algebra structure and let
`E : OrderAction D X` act on a formal `O`-module atlas over `A.obj`.
No maximal-order or finiteness condition on `D` is required here. The atlas
coordinate types are finite and may differ for map naturality, while the
original covers must agree. The covers need not be finite, and tests have the
underlying coefficient-algebra universe.

The canonical square uses `Nilp.scalarMap O f`, `Nilp.quotientO O B`,
`Nilp.quotientO O A` and `Nilp.reducedScalarMap O f`, with equality of the two
composites proved by `Nilp.quotientO_natural O f`. Each quotient is the actual
principal-ideal quotient by the image of `pi`. It need not be a residue field
or reduced; no flatness or injectivity of `f` is assumed.

`reductionBaseChangeIso E f` specializes the actual full-order square
isomorphism. Its source is `(E.baseChangeAlong (scalarMap O f)).reduction`
and its target is `E.reduction.baseChangeAlong (reducedScalarMap O f)`.
The underlying cover equality is `X.reductionBaseChangeOpens_eq f`.
The comparison consists of actual left composition, equality transport, and
inverse right composition isomorphisms, each commuting with every element of
`D`. It constructs both formal maps and both inverse equations, retaining the
specified chart choices. The lemmas `reductionBaseChangeIso_hom_val` and
`reductionBaseChangeIso_inv_val` identify both forgotten maps with the exact
ambient reduction/base-change comparison maps. They specialize the two
full-order square forgetful identities.

## Entire D-linear families and integral maps

For every test `C` over `B.obj/(pi)`, `reductionBaseChange_onPoints` compares
entire compatible families. A family for `E` on `C` restricted along the left
composite can first be extended along `f` and reduced, then carried across the
actual formal isomorphism. The result equals the family obtained by transporting
the original family along `quotientO_natural`, reducing it, and extending along
the induced quotient map. Every comparison in the equation is `D`-linear.
The explicit equality transport compares the two restricted coefficient tests.
`reductionBaseChange_inv_onPoints` gives the reverse equation for the inverse
of that same `D`-linear equivalence. Both proofs specialize the full-order
coefficient-square family equations. They concern complete families on all
chart tests rather than a single chart evaluation.

For every actual integral order-linear map `a : Hom E E' h`,
`Hom.reductionBaseChange_natural` says that its left-route extension followed
by the target comparison equals the source comparison followed by its
right-route extension. `Hom.reductionBaseChange_inv_natural` gives the reverse
square using both actual inverse comparison maps. The equalities are between
formal order-linear maps, including commutation with every `d : D`, and use
the induced cover equalities. Their proofs directly specialize the integral
full-order square laws at the four canonical maps and their proved equality.

## Full rational centralizer and whole quasi-isogenies

For any field `F` with `Algebra O F`, the domain
`OrderAction.RationalHom F E E' h` is the full chartwise `D`-centralizer inside
the global tensor `F tensor_O BasicAtlas.Hom X Y h`. It is not replaced by the
tensor of integral order-linear Hom. The two naturality equations in
`RationalHom` cover every element of this centralizer in the forward and
inverse directions. Each route uses the actual rational reduction and
supplied-target extension, and each comparison factor rationalizes an actual
integral map. The proofs specialize the full-order rational coefficient-square
laws. There is no integral-generation, local rational-gluing or
evaluation-injectivity premise, and no domain or fraction-field assumption
is needed in this section.

Under the additional assumptions `IsDomain O` and `IsFractionRing O F`,
`reductionBaseChangeQuasiIsogeny` applies `QuasiIsogeny.ofIso` to the actual
full-order comparison. Its `_hom` and `_inv` lemmas expose both rationalized
formal maps, retaining both inverse equations. Its `_toAtlas` lemma identifies
the whole forgotten quasi-isogeny with the ambient quotient comparison,
by specializing the whole-square forgetful identity. Finally the two laws in
`QuasiIsogeny` specialize the forward and inverse whole-quasi-isogeny square
laws. Their equality includes the inverse maps, as well as the forward maps.

This pair does not assert specialness, height, arbitrary-refinement invariance,
further coherence, framing, levels, rigidity or representability.
