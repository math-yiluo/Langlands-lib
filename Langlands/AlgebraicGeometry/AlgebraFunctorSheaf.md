# Extending an algebra functor to a Zariski sheaf over an affine base

For every commutative ring `R : Type u`, this module constructs a
presheaf `G : (Over (Spec R))ᵒᵖ ⥤ Type u` from an algebra functor `F` satisfying
finite principal-open descent. Its total presheaf `G.overTotal` is a sheaf
for `Scheme.zariskiTopology`. Evaluation on `Spec A` over `Spec R` is naturally
equivalent to `F A`. No finiteness, Noetherian, field or nontriviality
assumption is imposed on `R` or its algebras. The algebra types, value types
and schemes lie in one arbitrary universe `u` (the cited source uses universe zero; see below).

The exported theorem is
`AlgebraicGeometry.Scheme.exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away`.
Its inputs are the actual values `F A`, maps along every `R`-algebra
homomorphism, their identity and composition laws, and the following descent
condition. If `f : Fin n → A` spans the unit ideal, and `B i` is any
localization of `A` away from `f i` with compatible `R`-algebra structures,
compatible sections in `F (B i)` have a unique section in `F A`. Compatibility
is required after both structure maps to every localization away from
`f i * f j`. The quantification includes `n = 0` and arbitrary realizations
of these localization rings. This condition is the proposition definition
`AlgebraFunctorSheaf.Datum.IsSheaf` in the namespace below.

The outputs are `G`, equivalences `ev A`, the sheaf assertion for its total
presheaf, and the displayed naturality equation for every algebra
homomorphism `φ : A →ₐ[R] B`. The morphism on spectra is `Spec.map φ` and
naturality is stated in the over category with its commutative triangle.
This is an extension and sheaf theorem. A representing scheme, an affine
chart cover, properness, smoothness and the normalized Harris CM comparison
are further obligations of the host task.

The implementation helpers live in
`AlgebraicGeometry.Scheme.AlgebraFunctorSheaf`:

- `Datum` bundles the functor values, maps and laws. `F'`, `am`, `mkₐ` and
  `T` make algebra structures explicit so that a value can be transported
  between equal scalar maps. Their lemmas prove identity, composition and
  congruence directly from the input laws.
- `Datum.Tot A` consists of a ring homomorphism `R → A` and an `F A` value
  for the algebra structure it determines. `Datum.P₀` makes these pairs
  into a presheaf on `CommRingCatᵒᵖ`. `Tot.out` changes to a specified equal
  scalar structure, and `Tot.ext_of_out` proves equality of pairs by that
  transport.
- `J₀` is the topology induced along `Scheme.Spec` from the big Zariski
  topology. The scoped `isCoverDense_Spec` and `isOneHypercoverDense_Spec`
  instances follow from actual affine covers. `stdObj` and `stdHom` give
  finite principal-localization covers. `generate_std_mem` proves they
  cover; `exists_std_of_mem` refines any covering sieve by such a cover,
  using basic opens and a finite family spanning the unit ideal.
- `Datum.isSheafFor_std` first glues the scalar maps to `Spec R` using the
  representable Zariski sheaf. It then applies the input descent condition
  with that scalar map to glue the `F` values. Equality of scalar maps and
  uniqueness in the input descent condition prove uniqueness of the pair.
  `Datum.isSheaf_P₀` passes to arbitrary covering sieves. For separatedness
  after base change it maps the finite principal family to the new ring,
  where it still spans the unit ideal.
- `Datum.G₀` bundles that affine sheaf. `Datum.H` is its extension to
  schemes through Mathlib's `Functor.OneHypercoverDenseData.essSurj`.
  `H_isSheaf`, `Hiso`, `toH` and `ofH` give the sheaf property and the
  natural inverse equivalences on affine schemes. `aff` restricts a
  section to an arbitrary affine test morphism.
- `Datum.base` glues the scalar maps of these affine restrictions to a
  scheme morphism `T → Spec R`. `base_spec` proves compatibility with
  every affine test morphism: it checks on affine covers of the pullbacks,
  uses `pullback.condition`, and applies the affine restriction identity.
  `base_unique` proves uniqueness by the affine cover.
- The primary definition `Datum.G` takes those sections of `H` whose scalar
  morphisms agree with the given map to `Spec R` on every affine test.
  `totEquiv` and the natural isomorphism `totIso` identify its total
  presheaf with `H`. `isSheaf_overTotal` transports the sheaf property
  along that isomorphism. This reuses the published
  `Langlands.CategoryTheory.OverTotalPresheaf` without redefining it.
- `tot`, `germ`, `evFun` and `evInv` construct the affine evaluation
  equivalence `Datum.ev`. The two inverse laws use the restriction
  equivalence for `H` and the explicit scalar transports.
  `Datum.ev_natural` proves compatibility with every algebra homomorphism.
  The exported existence theorem packages this construction with the
  original, fully displayed hypothesis and conclusion.

The source is the registered Anthropic FLT complete Lean distribution
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, distribution SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete files used are:

- `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.lean`,
  lines 1–612, SHA-256 `56ba332080aef9d5b381d648aa8248051342b81ba87a1455ac1df6e8da092094`. This contains the actual
  construction and proof, including the `GrassBridgeH1.Datum` helpers.
- `Theorems/Thm_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.lean`,
  lines 1–37, SHA-256 `4c213899ad1a5dbcddd5af49bd6375b76176edada491db4983831c0dcc502470`. The port's exported theorem
  signature is byte-identical to this wrapper's full signature.

Worker 344 read the full implementation and wrapper, including the
compatibility differences from the earlier private feasibility copy.
The adaptation replaces `import Mathlib` with focused imports, reuses the
published total-presheaf module, renames the implementation namespace,
and removes the P2M commands and wrapper tactic. Helper simplification and
extensionality attributes are ordinary attributes instead of source-scoped
ones. Three rewrites use `erw` to expose the current bundled morphisms.
The long rewrite sequence in `base_spec` is replaced by an explicit typed
calculation using the same affine restrictions and pullback equation;
this avoids a rewrite elaboration timeout. A local algebra instance uses
current `let` syntax. The construction, input hypotheses
and exported conclusion are preserved.

The distribution is licensed under Apache 2.0, copyright 2026 Anthropic,
PBC. Its retained license and notices are in `licenses/Anthropic-FLT/`.
The distribution's attribution list has no separate entry for these two
files. The local project source-errata directories contain no entry for
this source. Imported Library Lean/Markdown pairs remain unchanged.

## Universe generalization (task `6d6cc279-3071-445f-adba-589e54d9816b`)

Worker 1109 generalized this module from universe zero to an arbitrary universe `u`, so that the
universe-polymorphic port of the FLT Hom-scheme construction (used by
`Langlands.AbelianScheme.relativeEndomorphismRepresentability`) can use these results in place of
duplicate copies of the same FLT theorems. Statements are otherwise unchanged; for `u = 0` they are
the previous ones, so existing universe-zero uses still apply.

- A line `universe u` is added after the imports.
- Every universe-zero `Type` in binders, quantifiers, structure fields and type ascriptions becomes
  `Type u`, and every `Scheme.{0}` becomes `Scheme.{u}`.
- Explicit universe-zero instantiations become universe `u`: `CommRingCat.{0}`, `Scheme.zariskiTopology.{0}` and `Functor.IsOneHypercoverDense.{0}` become `.{u}`, and the sheaf `G₀ : Sheaf J₀ (Type 0)` becomes `Sheaf J₀ (Type u)`.
- In `generate_std_mem` the standard open cover `(Scheme.affineOpenCoverOfSpanRangeEqTop f hf).openCover`, indexed by `Fin n`, is replaced by its `ulift` (Mathlib's `Cover.ulift`), because a covering in the Zariski topology on `Scheme.{u}` must be indexed by a type in universe `u`; for each index `x` of the lifted cover the proof uses the original index `(…).openCover.idx x`. The sieve membership proved is unchanged.
- In total 84 lines of the published file are changed (the two-line cover step of `generate_std_mem` becomes three lines) and 2 lines added; no proof step changes otherwise.
