# Local two-axis triviality for smooth proper families: proof

Author: Worker 513. Worker 1017 contributed the initial proper-spreading
interface and the design used to apply it in this assembly.

The module proves

```lean
theorem Langlands.AlgebraicGeometry.Picard.localTwoAxisTriviality :
    Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement.{u}
```

It imports the published statement unchanged and retains the arbitrary
universe `u`. For every base scheme `S`, smooth proper geometrically connected
families `X Y : Over S`, sections `x₀`, `y₀`, line bundle `L` on their product
and point `s : S`, triviality on the two full section axes and the
scheme-theoretic fibre at `s` implies triviality on the full product over an
open neighbourhood of `s`.

## Published proofs used

The proof imports three unconditional theorems by their Lean module names:

- `Langlands.AlgebraicGeometry.Picard.fieldTwoAxisH1Injectivity`, in
  `FieldTwoAxisH1InjectivityProof`, detects degree-one cohomology over a field
  using the actual adjunction units of the two axes. Its implementation uses
  affine Čech cocycles and the degree-one Künneth argument.
- `Langlands.AlgebraicGeometry.Picard.fibreFrameLifting`, in
  `FibreFrameLiftingProof`, constructs a section on a neighbourhood whose
  pullback to the specified fibre is an isomorphism. Its proof supplies
  restriction-compatible perfect models, algebraic spreading and an actual
  section. These are conclusions of that imported proof.
- `Langlands.AlgebraicGeometry.Modules.properLineBundleMorphismSpread`, in
  `ProperLineBundleMorphismSpreadProof`, spreads the invertibility of the
  same section from a fibre to an open neighbourhood under a universally
  closed structure morphism.

All three propositions are discharged by these published proofs. Their
implementations and provenance are documented in their respective paired
Markdown files.

## Implemented proof

The private helper `product_geometry` uses the actual categorical product
square in `Over S` to show that the product structure morphism is smooth,
proper and geometrically connected, by base change and composition.
`first_axis_closed` and `second_axis_closed` show that the axes are closed
immersions: each axis is a section of a separated product projection.

The private construction `fibre_map` defines the map of scheme-theoretic
fibres induced by an `S`-morphism using the pullback universal property.
`product_fibre_isPullback` proves that the precise product fibre occurring
in the target, `((X ⨯ Y).hom.fiber s)`, is a pullback of the two factor
fibres over `Spec κ(s)`. The construction `fibre_section` base changes the
two given sections. The identities `first_axis_fibre` and
`second_axis_fibre` identify the maps of the original axes on fibres with
the section-axis lifts in this pullback square.

`product_fibre_H1_detection` applies `fieldTwoAxisH1Injectivity` over the
actual residue field `S.residueField s`. Smoothness, properness and geometric
connectedness of the factor fibres follow by base change. The projection
and axis identities rewrite the result to exactly the adjunction-unit
kernel criterion required by `fibreFrameLifting`, on the actual fibre used
by the target.

Apply `fibreFrameLifting` to the product, the two closed axes and the
three given trivializations. It gives an open `U` containing `s` and an
actual morphism `σ` from the structure module to the pulled-back line
bundle on `P_U = (X ×_S Y) ×_S U`, whose pullback to the fibre over
`⟨s, hs⟩` is an isomorphism. The morphism `P_U ⟶ U` is proper by base
change, hence universally closed. Apply `properLineBundleMorphismSpread`
to this same `σ`. It gives an open `V` in `U` containing that point, on
which the pullback of `σ` is an isomorphism. Its inverse, followed by
`pullbackUnitIso`, trivializes the line bundle on the iterated pullback.

Finally, `nested_open_triviality` flattens these two open restrictions.
Set `g = V.ι ≫ U.ι` and `W = g.opensRange`, an open of `S` containing `s`.
The pullback pasting isomorphism and the isomorphism from `V` onto `W`
identify the iterated pullback with `P ×_S W`, compatibly with its map to
`P`. Pull the trivialization along the inverse isomorphism and compose
with `Scheme.Modules.pullbackComp`, `pullbackCongr` and
`Langlands.Scheme.Modules.pullbackUnitIso`. This produces exactly the
module isomorphism required by the target.

Every restriction is a base change of schemes and module sheaves. The
argument retains the full scheme structures, including nilpotents, and
places no additional condition on the base. Lean reports only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The elaborator option
`backward.isDefEq.respectTransparency false` assists definitional
unfolding and adds no mathematical hypothesis.

## Provenance

The proof follows the Stacks Project, More on Morphisms, Lemma
`lemma-pic-of-product` (tag 0BF3), retained `more-morphisms.tex` lines
9621–9650. The lifting input implements the preceding tag 0BF2, lines
9518–9619; the universal hypotheses are those of tag 0BDP, lines
9198–9215. Registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`.
Worker 513 read these statements and complete proofs, together with the
single-H1 argument in lines 9430–9516. The retained README records two
corrected typographical comments on 0BDP; no project errata file was
present when checked.

The source invokes Künneth on the fibre and then applies 0BF2 to the two
axes. Here the published field theorem supplies exactly the needed
kernel criterion, and the published lifting and proper-spreading
theorems implement the two stages of 0BF2. The private product, fibre,
axis and open-flattening helpers are internal consequences of categorical
pullback and scheme lemmas, rather than separate assertions quoted from
the source.
