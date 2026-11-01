# Component API for cocycle-compatible module sheaves

This internal API supplement imports
`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof` and reuses its actual
compatible-family sheaf. All new declarations are in
`Langlands.SchemeModule.CocycleSheaf`.

## Data and compatibility

Let `X : Scheme.{u}`, `ι : Type u`, `T : ι → X.Opens`, and
`g : ∀ i j, (Γ(X, T i ⊓ T j))ˣ`. No cover or cocycle identity is assumed.
The opens may be empty, the index type may be empty or infinite, and no
finiteness, affineness or other geometric hypotheses are required.

`Family T U` abbreviates the imported `CocycleGluing.Fam T U`, namely the type
`∀ i, Γ(X, U ⊓ T i)`. It inherits that type's additive group and
`Γ(X, U)`-module structure. The scalar action sends component `b i` to
`r|_(U ⊓ T i) * b i`.

`Compatible g b` is a Prop-valued predicate. For each `i j`, it requires

`b i|_(U ⊓ T i ⊓ T j) = g i j|_(U ⊓ T i ⊓ T j) * b j|_(U ⊓ T i ⊓ T j)`.

The three restriction maps are induced by the evident inclusions into
`U ⊓ T i`, `T i ⊓ T j`, and `U ⊓ T j`, respectively. Meets in the Lean
formula associate to the left.

`compatible_iff g b` proves equivalence with the imported
`CocycleGluing.Compat g b`, which imposes this equation on every common
subopen of `U ⊓ T i` and `U ⊓ T j`. One direction restricts the displayed
overlap equation further and uses preservation of multiplication and composition
of restrictions. The converse specializes to `U ⊓ T i ⊓ T j`.

## The actual sheaf and its section API

`moduleSheaf g : X.Modules` abbreviates `CocycleGluing.glued g`. Its module
and sheaf structures are the published ones. The definition depends only on
`X`, `T`, and `g`. It supplies the usual module structure on
`Γ(moduleSheaf g, U)`.

The API is:

- `component g U i s : Γ(X, U ⊓ T i)` is the imported coordinate `comp g s i`.
- `mkSection g U b hb : Γ(moduleSheaf g, U)` uses the imported constructor
  `mk g b` after converting `hb : Compatible g b` with `compatible_iff`.
  `component_mkSection` evaluates every coordinate to `b i`.
- `section_ext g U` proves equality of sections from equality of every
  coordinate.
- `component_zero` and `component_add` express preservation of zero and
  addition.
- `component_smul` states
  `component g U i (r • s) = r|_(U ⊓ T i) * component g U i s`
  for `r : Γ(X, U)`.
- `component_restrict g h i s` states that for
  `h : V ≤ U` the `i`-th coordinate of the restricted section is the
  restriction of `component g U i s` along `V ⊓ T i ≤ U ⊓ T i`.
- `component_compatible g U s` proves that the family of coordinates of any
  section is compatible. `component_overlap g U s i j` displays its equation
  on a particular overlap.
- `mkSection_components` proves that rebuilding a section from its
  coordinates returns that section.

`sectionsEquiv g U` explicitly identifies

`Γ(moduleSheaf g, U) ≃ {b : Family T U // Compatible g b}`.

It sends a section to its coordinates and sends a compatible family to
`mkSection`. The left inverse follows from `section_ext`; the right inverse
is equality of subtype elements with identical coordinates. The formulas
`sectionsEquiv_apply` and `sectionsEquiv_symm_apply` expose the two directions.
Together with the component formulas this interface describes all sections,
the scalar action, and restriction without unfolding the sheaf-condition proof.

The coordinate evaluation and zero, addition, scalar and restriction formulas
are definitional equalities in the imported construction. Extensionality reuses
`CocycleGluing.eq_of_comp`, and compatibility reuses
`CocycleGluing.compat_of_mem` followed by `compatible_iff`.

## Provenance and scope

This is an internal, derived API for the construction implemented by Worker 303
in the published `CocycleLineBundleProof.lean` and documented in its paired
Markdown. The module imports that construction by Lean name and neither copies
nor changes its sheaf proof. The only new mathematical bridge is the
equivalence between checking compatibility on an overlap and checking all of
its subopens; it follows directly from structure-sheaf restriction maps.

The imported companion and `CocycleLineBundleStatement.md` explain the
line-bundle application and its source rationale. This supplement does not
assert local rank one without hypotheses, prove a classification theorem, or
reprove the line-bundle and generation-open results. The arbitrary unit family
here need not satisfy a cocycle identity and the opens need not cover the
scheme; the compatible-family module sheaf still exists.

## Authorship

Worker 1203 wrote this API supplement and companion. The imported construction
remains the published work of Worker 303.
