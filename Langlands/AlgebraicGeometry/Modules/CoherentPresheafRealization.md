# Quasi-coherent module presheaves as actual module sheaves

Author: Worker 1405.

This module is `Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization`.

## Main result

`exists_modules_sectionsEquiv`: let `X` be a locally noetherian scheme with a
morphism `π : X ⟶ Spec R`. Let `G : OModulePresheaf π` satisfy
`G.IsQuasicoherent` and `G.IsCoherent`. Then there are a sheaf of modules
`M : X.Modules` and, for every affine open `U`, a `Γ(X, U)`-linear equivalence
`e U : Γ(M, U) ≃ₗ[Γ(X, U)] G.obj U` such that:

- `M.IsFinitePresentation` (Mathlib's local finite presentation);
- for affine opens `V ≤ U` and `s : Γ(M, U)`, the equivalences commute with
  restriction: `e V (M.presheaf.map (homOfLE h).op s) = G.res h (e U s)`.

`OModulePresheaf`, `IsQuasicoherent` and `IsCoherent` are the Library
definitions in
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`.
`G.IsQuasicoherent` asks, for every affine open `U` and `f : Γ(X, U)`, that
`G(U) → G(D(f))` be a localization at `f` in the form of two conditions
(every section over `D(f)` times a power of `f` comes from `U`; a section over
`U` that vanishes on `D(f)` is killed by a power of `f`). `G.IsCoherent` asks
that `G(U)` be a finite `Γ(X, U)`-module for every affine open `U`. Neither
condition says anything about non-affine opens.

## Purpose and provenance

This is the output bridge of the proof task `20cb772c` (proper coherent formal
existence). The Library's ported FLT existence theorem produces a coherent
quasi-coherent `OModulePresheaf`; the target statement asks for an actual
`X.Modules`. The result is a form of the standard fact that a quasi-coherent
sheaf is determined by its values on affine opens and can be recovered from
them by gluing. No particular literature statement is formalized: the
statement, the construction and the proofs below were written for this
development. They use only the two conditions of `IsQuasicoherent` and do not
depend on any FLT theorem.

## Construction

For an open `O`, a section of the realization over `O` is a family
`(s_V)` of sections `s_V ∈ G(V)`, one for each affine open `V ≤ O`, that is
compatible: `G.res h s_V = s_W` whenever `W ≤ V` are affine opens below `O`.
Functions on `O` act through their restrictions to each `V`, and restriction
to a smaller open forgets the affine opens that do not fit. On an affine open
`U`, the family is determined by its value at `U` itself, which gives `e U`.

## Proof outline

1. Sheaf property of `G` on an affine open `V` (`existsUnique_glue`). Let `P`
   be a downward closed family of affine opens covering `V`, and let `t` be
   compatible sections on the members of `P`. The basic opens `D(f) ⊆ V` with
   `P (D(f))` generate the unit ideal of `Γ(X, V)`. Uniqueness: a section
   vanishing on all of them is zero (`eq_zero_of_res_basicOpen`, from the
   injectivity half of quasi-coherence and
   `Submodule.mem_of_span_eq_top_of_smul_pow_mem`). Existence: finitely many of
   them generate the unit ideal; the surjectivity half gives sections
   `y_f ∈ G(V)` with `y_f = f^N t_f` on `D(f)`. Since `g^N y_f - f^N y_g`
   vanishes on `D(fg)`, the injectivity half gives a common exponent `M` with
   `(fg)^M (g^N y_f - f^N y_g) = 0`. Hence `w_f = f^M y_f` satisfies
   `g^{N+M} w_f = f^{N+M} w_g`, and a
   partition of unity `∑ c_f f^{N+M} = 1` glues `x = ∑ c_f w_f`
   (`exists_res_eq_of_finset`). Agreement on an arbitrary member `W` of `P`
   is again checked on basic opens of `W`.
2. The compatible families form a sheaf (`secPresheaf_isSheaf`). Given
   compatible families on the members of an open cover, glue each affine
   open `V` of the union by step 1, applied to the affine opens contained
   in `V` and in some member of the cover.
3. On an affine open the sections are those of `G` (`sectionsEquiv`), and
   the identification commutes with restriction
   (`sectionsEquiv_naturality`).
4. Local finite presentation (`isFinitePresentation_realization`). Take an
   affine open `U` through a given point, with chart `j = hU.fromSpec :
   Spec Γ(X, U) ⟶ X`. The restriction of the realization along `j` is
   localizing in Mathlib's sense (`IsLocalizing`): `j` sends `D(f)` to the
   basic open of the corresponding function, and quasi-coherence of `G` is
   exactly the localization property needed by
   `IsLocalizedModule.Away.mk_of_addCommGroup` (`isLocalizing_restrict`). By
   Mathlib's `isIso_fromTildeΓ_iff_isLocalizing`, the restriction is the
   tilde of its global sections. These sections are `G` of the image of
   `j`, a finite module over the noetherian ring `Γ(X, U)`
   (`finite_restrict`), hence finitely presented. The Library lemmas
   `exists_presentation_tilde`, `exists_presentation_opensRange` and
   `isFinitePresentation_of_forall_exists_presentation`
   (`FinitePresentationDescent`) turn this into local finite presentation.
5. `exists_modules_sectionsEquiv` packages steps 2-4.

## Declarations

### Local algebra on an affine open

- `presheaf_res_res`, `presheaf_res_refl`: composition and identity for
  restriction of functions.
- `basicOpen_mul_le_left`, `basicOpen_mul_le_right`: `D(fg) ≤ D(f)` and
  `D(fg) ≤ D(g)`.
- `eq_zero_of_res_basicOpen`: on an affine open, a section of a
  quasi-coherent `G` vanishing on the basic opens of a set generating the unit
  ideal is zero.
- `exists_res_eq_of_finset`: on an affine open, sections over the basic opens
  of a finite set generating the unit ideal that agree on the pairwise
  products `D(fg)` come from one section.
- `existsUnique_glue`: the sheaf property of `G` on an affine open `V` for a
  downward closed family `P` of affine opens covering `V` (step 1).

### The realization

- `AffBelow O`: the affine opens contained in `O`, as a subtype.
- `Fam G O`: families of sections of `G` indexed by `AffBelow O`, with the
  product group structure and the `Γ(X, O)`-action through restriction.
- `compat G O`: the submodule of compatible families.
- `secRes`, `secPresheaf`, `secModules`: restriction of compatible families,
  the abelian presheaf they form, and the presheaf of modules over
  `X.ringCatSheaf`.
- `secPresheaf_isSheaf`: the compatible families form a sheaf when `G` is
  quasi-coherent (step 2).
- `realization G hG : X.Modules`: the resulting sheaf of modules.
- `sectionsEquiv hG hU : Γ(realization G hG, U) ≃ₗ[Γ(X, U)] G.obj U` for an
  affine open `U`: evaluation at `U`, with inverse `x ↦ (G.res _ x)_V`.
  `sectionsEquiv_apply` is its defining equation.
- `sectionsEquiv_naturality`: compatibility with restriction between affine
  opens.
- `exists_res_eq_smul`, `exists_pow_smul_eq_zero`: the two halves of
  quasi-coherence for an open `D` that is equal (not definitionally) to a basic
  open.

### Spectrum charts

For an open immersion `j : Spec A ⟶ X`:

- `chartHom j : A →+* Γ(X, j ''ᵁ ⊤)`: the coordinate ring as functions on the
  image.
- `image_basicOpen_chart`: `j` sends `D(f)` to the basic open of
  `chartHom j f`.
- `smul_restrict_chart`: on the restriction of `M : X.Modules` along `j`, the
  action of `a : A` on sections over `V` is the action of the restriction of
  `chartHom j a` to `j ''ᵁ V`.
- `isLocalizing_restrict`: if `j ''ᵁ ⊤` is affine and `G` is quasi-coherent,
  the restriction of the realization along `j` is `IsLocalizing`.
- `finite_restrict`: if moreover `G(j ''ᵁ ⊤)` is a finite
  `Γ(X, j ''ᵁ ⊤)`-module, the global sections of the restriction of the
  realization along `j` are a finite `A`-module. The `A`-action and the
  `Γ(X, j ''ᵁ ⊤)`-action correspond under the Library lemma
  `restrict_smul_Spec`.

### Finite presentation

- `isFinitePresentation_realization`: on a locally noetherian scheme, the
  realization of a coherent quasi-coherent `G` is locally finitely presented
  (step 4).
- `exists_modules_sectionsEquiv`: the main result above.
