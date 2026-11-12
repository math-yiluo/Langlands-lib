# Eventual equality of morphisms and uniqueness of models of algebraic spaces

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Printed p.13, start of Section 5: "The first step is to verify that Theorem 3.4
is valid with finitely presented algebraic spaces in place of finitely
presented schemes." Conrad says this is proved by an étale descent argument and
refers to the proof of [Ols, Prop. 2.2]. Theorem 3.4 is on printed p.5. For a
directed system of rings `A_i` with colimit `A`:

- part (1), second sentence: for finitely presented `A_{i₀}`-objects `X_{i₀}`
  and `Y_{i₀}`, the natural map `colim Hom_{A_i}(X_i, Y_i) → Hom_A(X, Y)` is
  bijective;
- part (3): a descent `X_{i₀}` of a finitely presented `A`-object `X` is
  "essentially unique up to essentially unique isomorphism". For finitely
  presented `X_{i₀}` and `X'_{i₀}` whose base changes over `A` are identified
  with `X`, there is some `i ≥ i₀` and an isomorphism `h_i : X_i ≃ X'_i`
  compatible with the common identification over `A`; and if `h_i` and `H_i`
  are two such isomorphisms, then `h_{i'} = H_{i'}` for some `i' ≥ i`.

This file states, for algebraic spaces, the injectivity half of the bijection
in part (1) and the whole of part (3). Surjectivity in part (1) and the first
sentence of part (1) are the separate Library statements
`SpaceLimitMorphismDescent`, `SpaceLimitMorphismDescentQuasiSeparated`,
`SpaceLimitModelExistence` and `SpaceLimitModelExistenceQuasiSeparated`.
Property descent, part (2), is not stated here.

## Common setting

Both statements quantify, in one arbitrary universe `u`, over

- a small cofiltered category `I` and a diagram `D : I ⥤ Scheme` of affine
  schemes, with an actual limit cone `c` (`IsLimit c`);
- a stage `i : I` and algebraic spaces over the affine scheme `D.obj i`.

Base change along a scheme morphism is the Library's `baseChange`, and on
morphisms `baseChangeMap`. For `f : j ⟶ i` in `I`, the transition to stage `j`
is base change along `D.map f`, and the passage to the limit from stage `i` is
base change along the cone leg `c.π.app i`.

Conrad's ring setting is the case where `D` is the diagram of spectra of a
directed system of rings `A_i` and `c.pt` is the spectrum of its colimit `A`.
Every cofiltered diagram of affine schemes is the spectrum of a filtered
diagram of rings, so the general diagram is a derived restatement of the same
setting, as in the Library's other `SpaceLimit…` statements.

"Finitely presented" is encoded as in `SpaceLimitModelExistenceQuasiSeparated`.
A space is assumed quasi-separated (`IsQuasiSeparated`) and to have a
surjective étale scheme atlas whose structure map to the base is locally of
finite presentation and quasi-compact
(`HasAtlasProperty (LocallyOfFinitePresentation ⊓ QuasiCompact)`). Over the
affine base `D.obj i` these assumptions make the space quasi-compact,
quasi-separated and locally of finite presentation. Section 5 of Conrad works
with quasi-separated algebraic spaces throughout. Every space in both
statements, source and target, carries both assumptions.

## `SpaceLimitMorphismEventualEquality`

Let `X` and `Y` be finitely presented algebraic spaces over `D.obj i`, and let
`φ ψ : X ⟶ Y`. If `baseChangeMap (c.π.app i) φ = baseChangeMap (c.π.app i) ψ`,
then there are `j : I` and `f : j ⟶ i` with
`baseChangeMap (D.map f) φ = baseChangeMap (D.map f) ψ`.

This is injectivity of `colim Hom_{A_i}(X_i, Y_i) → Hom_A(X, Y)`. Two elements
of the colimit are represented at a common stage, and reindexing to that stage
replaces `X` and `Y` by their base changes there, which are again finitely
presented. So it suffices to compare two morphisms at one stage `i`, which is
what the statement does.

## `SpaceLimitModelUniqueness`

Let `X` and `X'` be finitely presented algebraic spaces over `D.obj i`, and let
`e : baseChange (c.π.app i) X ≅ baseChange (c.π.app i) X'` be an isomorphism
over the limit. Conrad's common identification of the two base changes with
one `X` amounts to giving such an `e`.

For `f : j ⟶ i`, the base change of a stage-`j` isomorphism
`h : baseChange (D.map f) X ≅ baseChange (D.map f) X'` along `c.π.app j` lives
on `baseChange (c.π.app j) (baseChange (D.map f) X)`. The Library comparison
`BaseChangeComparison.compIso (D.map f) (c.π.app j) (c.π.app i) (c.w f) X`
identifies this with `baseChange (c.π.app i) X`, using the cone equation
`c.w f : c.π.app j ≫ D.map f = c.π.app i`. "Compatible with `e`" means

`baseChangeMap (c.π.app j) h.hom = (compIso … X).hom ≫ e.hom ≫ (compIso … X').inv`.

The statement asserts:

1. **Existence.** There are `j`, `f : j ⟶ i` and an isomorphism `h` at stage
   `j` compatible with `e`.
2. **Essential uniqueness.** For any `j`, `f : j ⟶ i` and two isomorphisms
   `h h'` at stage `j` that are both compatible with `e`, there are `k` and
   `f' : k ⟶ j` with
   `baseChangeMap (D.map f') h.hom = baseChangeMap (D.map f') h'.hom`.

Equality of the `hom` components determines the isomorphisms.

## Combined target

`SpaceLimitUniquenessStatement` is the conjunction of the two propositions. No
proof is supplied here.

## Provenance

The statements are Conrad's, transported to the Library's algebraic spaces.
The derived choices are: the general cofiltered diagram of affine schemes in
place of a directed system of rings; reduction of the colimit injectivity to
two morphisms at one stage, as explained above; the encoding of finite
presentation through quasi-separatedness and an atlas property; and the
expression of compatibility with the common identification through
`compIso`.
