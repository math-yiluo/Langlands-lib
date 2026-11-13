# The sheaf of the regular module `D(X)` is `C^∞_X`

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This file covers the first Example after the stalk description in II.2.5, printed p.41 /
PDF p.47:

> Exemple. Si M = D(X) alors ℳ est le faisceau C^∞_X des fonctions localement
> constantes sur X.

Here `ℳ` is the sheaf that the Theorem of II.2.5 attaches to a nondegenerate
`D(X)`-module `M`, with `ℳ(U) = χ_U · M` on compact opens `U`. The file builds `C^∞_X` as
a sheaf of complex vector spaces and gives an explicit isomorphism between it and the
published sheaf of the regular module. Everything here is either a definition or proved
in the file. It adds no proposition for a later proof task.

## Setting

`X : Type u` is any topological space for the construction of `C^∞_X`. The comparison
takes `hX : Langlands.Topology.IsLocallyProfinite X`, the Library's predicate for
Renard's t.d. spaces, which the published construction of `ℳ` needs.

- Renard's `D(X)` is the published pointwise test algebra
  `PointwiseTestAlgebra.Carrier X`: compactly supported locally constant complex
  functions with pointwise operations.
- The regular module is `D(X)` acting on itself by left multiplication. This is the
  published adapter `NonUnitalModule.regular`. It is a local instance in this file only.
- The sheaf `ℳ` is the published `ProjectorVectorSheaf.sheaf hX hM`. Its sections over an
  open `V` are compatible families `(s_U)` of elements `s_U ∈ χ_U · M`, one for each
  compact open `U ⊆ V`. Its complex structure is Renard's canonical one
  (`ProjectorVectorSheaf.originalModule`, from I.2.1).
- Sheaves of complex vector spaces are the published `VectorSheafScalars.VectorSheaf X`.
  By the II.2.5 Proposition (`VectorSheafScalars`), every such sheaf is a sheaf of
  `C^∞_X`-modules, with `C^∞(U)` acting on sections over `U`.

## The sheaf `C^∞_X`

- `scalarPresheaf X` sends an open `U` to the complex vector space
  `LocallyConstant U ℂ` of locally constant complex functions on `U`. Restriction is
  pullback along the inclusion (Mathlib's `LocallyConstant.comapₗ`). This is the same
  restriction as in the published scalar ring presheaf
  (`scalarPresheaf_map_eq_restrict`, with `LocallyConstantScalar.restrict`).
- `underlyingIso X` identifies the underlying presheaf of sets with Mathlib's presheaf of
  functions satisfying the published local predicate of local constancy
  (`Equivariant.LocallyConstantSheaf.localPredicate`). `scalarPresheaf_isSheaf` follows
  from Mathlib's `TopCat.subpresheafToTypes.isSheaf`, since the forgetful functor from
  complex vector spaces reflects the sheaf condition.
- `scalarSheaf X : VectorSheaf X` is Renard's `C^∞_X`.
- `scalarSheaf_smul`: the published action of `C^∞(U)` on the sections of
  `C^∞_X` over `U` (`VectorSheafScalars.smul`) is multiplication of functions. So
  `scalarSheaf X` is `C^∞_X` as a sheaf of `C^∞_X`-modules, not only as a sheaf of vector
  spaces.

## The sheaf of the regular module

- `isNondegenerate_regular`: the regular module is nondegenerate. This is the published
  `NondegenerateTensorFunctor.regular_isNondegenerate` for the idempotented algebra
  `D(X)` (`PointwiseTestAlgebra.isIdempotented`).
- `regularSheaf hX` is Renard's `ℳ` for `M = D(X)`: the published
  `ProjectorVectorSheaf.sheaf` of the regular module. Since `D(X)` lives in the universe
  of `X`, this is a `VectorSheaf X`.
- `regular_smul`: Renard's canonical complex structure on the regular module is the
  usual scalar multiplication of functions. The proof uses
  `NondegenerateScalars.complex_smul_eq`: `c · g = (c e) g = c (e g) = c g` for an
  idempotent `e` with `e g = g`.

## The comparison

Let `s` be a section of `ℳ` over an open `V`, with components `s_U ∈ χ_U · D(X)`. The
corresponding function on `V` takes, at `x`, the value `s_U(x)` for any compact open
`U ⊆ V` containing `x`.

- `value_apply_of_not_mem`: an element of `χ_U · D(X)` vanishes off `U`.
- `component_apply_eq`: two components `s_U` and `s_W` agree at every point of
  `U ∩ W`. Both agree with `s_{U ∩ W} = χ_{U ∩ W} s_U = χ_{U ∩ W} s_W` there
  (`component_apply_of_le`).
- `neighborhood hX x` is a chosen compact open `U` with `x ∈ U ⊆ V`, from the basis of
  compact opens. `sectionValue s x = s_U(x)` for this `U`. By `sectionValue_eq` the value
  does not depend on the choice.
- `isLocallyConstant_sectionValue`: on the open set where `x ∈ U` and `s_U` takes the
  value `s_U(x)`, the function is constant. `sectionFun s : LocallyConstant V ℂ`
  packages it. `sectionFun_apply` reads it off any component.

The inverse extends functions by zero:

- `extendLC U f` extends `f ∈ LocallyConstant U ℂ`, for a compact open `U`, by zero
  outside `U`. It is Mathlib's `LocallyConstant.piecewise` on the closed sets `U` and its
  complement.
- `extendTest U f` is the same function as an element of `D(X)`. Its support is compact
  because it lies in the compact set `U`.
- `extendValue U f` is this element of `χ_U · D(X)`.
- `extendSection f`, for `f ∈ LocallyConstant V ℂ`, is the section of `ℳ` over `V` whose
  component on each compact open `U ⊆ V` is the extension by zero of `f|_U`. It is built
  with the published `ProjectorVectorSheaf.sectionMk`. `extendSection_apply` gives its
  values.

The isomorphism:

- `sectionScalarEquiv hX V : ℳ(V) ≃ₗ[ℂ] LocallyConstant V ℂ` is `sectionFun` with
  inverse `extendSection`. Complex linearity uses `regular_smul`. `sectionScalarEquiv_apply`
  gives its values.
- `sectionScalarEquiv_restrict`: the function of a restricted section is the restricted
  function.
- `presheafIso hX` is the natural isomorphism of presheaves of complex vector spaces
  with these components.
- `regularSheafIso hX : regularSheaf hX ≅ scalarSheaf X` is Renard's statement: the
  isomorphism of sheaves of complex vector spaces between `ℳ` for `M = D(X)` and
  `C^∞_X`. `regularSheafIso_hom_app` says that its component over `V` is
  `sectionScalarEquiv hX V`.

What the isomorphism does:

- `sectionScalarEquiv_originalSection`: the section of `ℳ` over `V` defined by an
  element `m ∈ D(X)` (the published `ProjectorVectorSheaf.originalSection`, with
  components `χ_U · m`) goes to the restriction `m|_V`.
- `sectionScalarEquiv_sectionLinearEquiv`: on a compact open `U`, an element
  `g ∈ χ_U · D(X) = ℳ(U)` (the published identification
  `ProjectorVectorSheaf.sectionLinearEquiv`) goes to the restriction `g|_U`.
- `sectionScalarEquiv_smul`: the isomorphism takes the action of `f ∈ C^∞(V)` on
  `ℳ(V)` (`VectorSheafScalars`) to multiplication by `f`. So `regularSheafIso` is also an
  isomorphism of sheaves of `C^∞_X`-modules. This follows from the published
  `VectorSheafScalars.app_smul` and `scalarSheaf_smul`.

## Scope

This file does not cover the description `ℳ_x ≃ M/M(x)` of the stalks on the same page,
or the second Example of p.41 (a continuous map `q : X → Y`).
