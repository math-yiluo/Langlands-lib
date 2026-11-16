# Reduction and change of the actual nilpotent coefficient algebra

This is an internal specialization of `AtlasBaseChangeAlongSquare` and
`AtlasReduction` at the canonical quotient square constructed in
`ModuleReduction`. It supplies the comparison needed when the actual `Nilp`
coefficient object varies, without making an additional original-literature
assertion.

## Coefficients and actual quotient maps

Let `O` and `R` be commutative rings with `Algebra O R`, let `pi` be any element
of `R`, and let `f : A -> B` be a morphism in `Nilp R pi`. The objects carry
commutative `R`-algebras on which `pi` is nilpotent. Their structural
`O`-algebras and those of their quotients are the composed algebra structures.
The quotient of `A` is the actual ring
`A.obj / Ideal.span {algebraMap R A.obj pi}`, and likewise for `B`.
The quotient need not be reduced or a residue field.

For a formal `O`-module atlas `X` over `A.obj`, use the supplied maps

```text
A.obj ---scalarMap O f---> B.obj
  |                         |
quotientO O A             quotientO O B
  |                         |
  v                         v
A.obj/(pi) -----------> B.obj/(pi)
           reducedScalarMap O f
```

`Nilp.quotientO_natural O f` proves equality of these composites as
`O`-algebra maps. No flatness or injectivity is assumed for `f`.
The finite coordinate types for `X` and a second atlas `Y` may differ; their
original principal covers must agree for the map naturality laws. Covers need
not be finite. If the underlying coefficient algebras have universe `w`, all
atlas tests here have universe `w`.

## Actual formal comparison and entire families

`reductionBaseChangeOpens_eq` identifies the covers of reduction after
extension along `f` and extension of the reduction along the induced quotient
map. It specializes the actual image-cover equality for the displayed square.
`reductionBaseChangeIso X f` specializes the corresponding actual formal
isomorphism. Its source is `(X.baseChangeAlong (scalarMap O f)).reduction`
and its target is `X.reduction.baseChangeAlong (reducedScalarMap O f)`.
Both formal maps and their two inverse equations are constructed from the
existing composition isomorphisms and equality transport. In particular, the
comparison retains the chart choices of those composition isomorphisms.

For every algebra test `C` over `B.obj/(pi)`,
`reductionBaseChange_onPoints` compares whole compatible families. Start with
a family for `X` on `C` restricted along the left composite. Extending first
along `f` and then reducing, followed by the actual formal comparison, gives
the family obtained by first transporting the original family along
`quotientO_natural`, then reducing and extending along the quotient map.
The equality transport is explicit because the two restricted tests have
equal structural maps. The equation concerns an entire compatible family on
all chart tests, not a single chart evaluation.
`reductionBaseChange_inv_onPoints` states the reverse equation for the inverse
of the same `O`-linear family equivalence. Both proofs directly specialize the
corresponding coefficient-square laws.

## Integral and global rational naturality

For every actual integral formal atlas map `a : Hom X Y h`,
`Hom.reductionBaseChange_natural` says that its left-route extension followed
by the target comparison equals the source comparison followed by its
right-route extension. `Hom.reductionBaseChange_inv_natural` gives the reverse
square with both actual inverse comparison maps. These are equalities of
formal maps over the induced cover equalities. Their proofs specialize the
integral square laws at the four canonical maps and their proved equality.

For a field `F` with `Algebra O F`, the rational Hom is the entire global
tensor `F tensor_O BasicAtlas.Hom`. The two laws in `RationalHom` give the
same forward and reverse squares for every element of that tensor. Each route
uses the actual rational reduction and supplied-target extension maps; each
comparison factor is the rationalization of an actual integral comparison
map. The proofs specialize the global rational coefficient-square laws and
require no local rational-gluing or evaluation-injectivity premise. No domain
or fraction-field hypothesis on `O` is needed in this section.

## Whole quasi-isogenies and boundaries

With the additional assumptions `IsDomain O` and `IsFractionRing O F`,
`reductionBaseChangeQuasiIsogeny` rationalizes the actual comparison through
`QuasiIsogeny.ofIso`. Its `_hom` and `_inv` lemmas identify both rational maps;
both inverse equations are retained. The two naturality laws in
`QuasiIsogeny` specialize the square laws as equalities of whole
quasi-isogenies, so their inverse maps are included in the conclusion.

This pair constructs the quotient comparison for ambient formal `O`-module
atlases. Full-order equivariance, specialness, height, arbitrary-refinement
invariance, further coherence, framing, levels, rigidity and representability
are outside this pair.
