# Complex vector sheaves and sheaves of `𝒞^∞_X`-modules are equivalent

Module `Langlands.Sheaf.Renard.VectorSheafModuleEquivalence`, namespace
`Langlands.Sheaf.Renard.VectorSheafModuleEquivalence`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This file covers the Remark after the Proposition of II.2.5, printed p.39 / PDF p.45:

> Remarque. Il est évident que réciproquement, un faisceau de `𝒞^∞_X`-modules est
> naturellement un faisceau de `ℂ`-espaces vectoriels sur `X`. En effet `ℂ` s'injecte
> naturellement dans tous les `𝒞^∞(U)` en associant à un scalaire de `ℂ` la fonction
> constante égale à ce scalaire sur `U`. Ainsi les notions de faisceau de `ℂ`-espaces
> vectoriels sur `X` et de faisceau de `𝒞^∞_X`-modules sont équivalentes (i.e. les
> catégories respectives sont équivalentes). De plus, en vertu du dernier paragraphe de
> II.2.1, ceci reste vrai pour les faisceaux de base `T`.

Here `T` is the set of all opens of `X`. The Proposition just before (printed pp.38–39 /
PDF pp.44–45) makes a sheaf of complex vector spaces of base `T_c` (compact opens) a sheaf
of `𝒞^∞_X`-modules by `(f s)(x) = f(x) s(x)`.

The file constructs the actual equivalence of categories for sheaves on **all opens**
(base `T`), which is the clause "ceci reste vrai pour les faisceaux de base `T`". Every
declaration is a definition or a proved theorem. There is no proposition for a later proof
task.

## Remaining obligation: the base `T_c`

The Remark's first equivalence is for sheaves of base `T_c`. This file does **not**
construct it. It would need an equivalence between module sheaves on the compact-open basis
and module sheaves on all opens, i.e. the module version of the final paragraph of II.2.1.
The Library has only the additive version (`BasisAllOpen.equivalence` in
[BasisAllOpenEquivalence](BasisAllOpenEquivalence.md)). The base-`T_c` form of the Remark
therefore remains open. The Library's complex vector sheaves are already sheaves on all
opens (see `VectorSheafScalars.VectorSheaf` below), so the file follows that convention.

## Setting

`X : Type u` is an arbitrary topological space. Renard assumes `X` t.d.; the
construction does not use it. Sections live in universe `u`, as in the published
`VectorSheaf X`.

- `VectorSheafScalars.VectorSheaf X` (published, [VectorSheafScalars](VectorSheafScalars.md)):
  Mathlib's `TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)`, sheaves of complex vector
  spaces on all opens. The published action of `f ∈ 𝒞^∞(U) = LocallyConstant U ℂ` on
  sections over `U` is `VectorSheafScalars.smul`, glued from the constant multiples
  `f(x) • s` on the open fibres of `f`, with germ formula `(f s)(x) = f(x) s(x)`.
- `scalarRingedBasis X`: Renard's ringed space `(X, 𝒞^∞_X)` on the published basis of all
  opens `allOpenBasis X`. Its ring presheaf is the published
  `LocallyConstantScalar.basisRingPresheaf (allOpenBasis X) ℂ` (`U ↦ LocallyConstant U ℂ`,
  restriction by pullback). Its sheaf proof is the published
  `LocallyConstantScalar.sheafCondition`.
- `ModuleSheaf X`: Renard's category `𝒞^∞_X − Mod(X)` on all opens. It is the published
  II.2.3 category `RingedBasis.ModuleSheaf (scalarRingedBasis X)`
  ([RingedBasisModules](RingedBasisModules.md)). Its objects are Mathlib presheaves of
  modules over the ring presheaf whose underlying additive presheaf satisfies Renard's sheaf
  condition. Its morphisms are morphisms of presheaves of modules.
  [RingedBasisModuleGluing](RingedBasisModuleGluing.md) supplies the all-open accessors
  `AllOpenModuleSheaf.sections`, `restrict`, `app` used below.
- `scalar f` reads `f : LocallyConstant U ℂ` as an element of the section ring
  `(scalarRingedBasis X).ring.obj (op (allOpen U))`. It is the identity. It only fixes the
  type, so that `scalar f • m` uses the module structure of the module sheaf.

## From vector sheaves to module sheaves

- `additiveSheaf F` is the underlying additive Mathlib sheaf, and `basisSheaf F` the same
  sections as a Renard sheaf on the basis of all opens, through the published
  `AllOpenMathlib.fromMathlib`.
- `basisModule` puts the published action `VectorSheafScalars.module` on these sections.
  `semilinearRestrictions` is the published `VectorSheafScalars.restrict_smul`: restriction
  is semilinear along the ring restriction.
- `toModuleObj F` is the published adapter `BasisModuleSheaf.ofBasisSheaf`
  ([RingedBasisModuleAdapter](RingedBasisModuleAdapter.md)) applied to these data. This is
  the Proposition of II.2.5 read in the category `ModuleSheaf X`.
- `toModuleMap φ` is the same morphism of additive sheaves. It preserves the action by the
  published `VectorSheafScalars.app_smul`.
- `toModule X : VectorSheaf X ⥤ ModuleSheaf X`.

The definitional lemmas `toModule_sections`, `toModule_restrict`, `toModule_map_app` say
that the sections, restrictions and morphism components are unchanged. `toModule_smul` says
that the action is the published glued action. `toModule_forget` says that forgetting the
action gives `sheafCompose forget₂ ⋙ AllOpenMathlib.fromMathlib`, the published additive
sheaf.

## From module sheaves to vector sheaves

This is the first sentence of the Remark: a sheaf of `𝒞^∞_X`-modules is a sheaf of complex
vector spaces through the constant functions.

- `vectorSections M U` is Mathlib's restriction of scalars
  `ModuleCat.restrictScalars (LocallyConstantScalar.constants ℂ U)` applied to the sections
  of `M` over `U`. So `c • m = scalar (constants c) • m` (`vectorSections_smul`).
- `vectorRestrictLinear` / `vectorRestrict`: the original restriction of `M` is complex
  linear, because the ring restriction maps constants to constants (the published
  `LocallyConstantScalar.restrict_constants`).
- `vectorPresheaf M` is the resulting presheaf of complex vector spaces on all opens.
  `vectorPresheaf_forget₂` says that its underlying additive presheaf is, definitionally, the
  published Mathlib additive sheaf `AllOpenMathlib.toMathlib` of the underlying basis sheaf
  of `M`. `vectorPresheaf_isSheaf` then follows from Mathlib's
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`.
- `toVectorObj M : VectorSheaf X`. `toVectorApp f U` is the component of a morphism `f` of
  module sheaves under restriction of scalars. `toVectorMap f` is the morphism of vector
  sheaves. Naturality is the published `BasisModuleSheaf.app_restrict`.
- `toVector X : ModuleSheaf X ⥤ VectorSheaf X`.

`toVector_sections`, `toVector_restrict`, `toVector_map_app` are the definitional
description. `toVector_forget` says that forgetting the complex structure gives the
published additive sheaf `moduleSheafToBasisSheaf ⋙ AllOpenMathlib.toMathlib`.

Renard justifies the first sentence by the injectivity of `ℂ → 𝒞^∞(U)`. The construction
only uses the ring homomorphism `constants`, never its injectivity. This matters for the
empty open, where `𝒞^∞(∅)` is the zero ring and the constants map is not injective (the
published `LocallyConstantScalar.constants_empty_not_injective`).

## The equivalence

- `unitLinearEquiv F U` / `unitApp F U`: the identity map of the sections of `F` over `U`,
  as an isomorphism of complex vector spaces from `F` to `toVector (toModule F)`. It is
  complex linear because constants act through the original complex structure (the
  published `VectorSheafScalars.constants_smul`). `unitObjIso F` assembles these into an
  isomorphism of sheaves.
- `smul_toVector M f m`: for a module sheaf `M`, the published glued action of `f` on
  `toVector M` is the given action, `VectorSheafScalars.smul (toVector M) f m = scalar f • m`.
  Proof: by the published characterization `VectorSheafScalars.eq_smul_iff`, it suffices to
  compare germs at each `x ∈ U`. Restrict to the open fibre `W` of `f` through `x`. There
  the restriction of `f` is the constant function `f(x)`. Semilinearity of the restriction
  of `M` (`AllOpenModuleSheaf.restrict_smul`) turns the restriction of `scalar f • m` into
  `scalar (constants (f x)) • m|_W`, which is `f(x) • m|_W` for the complex structure of
  `toVector M`. Germs are complex linear.
- `counitLinearEquiv M U` / `counitApp M U`: the identity map of the sections of `M`, as an
  isomorphism of `𝒞^∞(U)`-modules from `toModule (toVector M)` to `M`. It is linear by
  `smul_toVector`. `counitObjIso M` assembles these into an isomorphism of module sheaves,
  with Mathlib's `PresheafOfModules.isoMk`.
- `equivalence X : VectorSheaf X ≌ ModuleSheaf X` is the equivalence of categories, with
  functor `toModule X`, inverse `toVector X`, and the unit and counit above.
  `equivalence_functor`, `equivalence_inverse`, `equivalence_unitIso_hom_app` and
  `equivalence_counitIso_hom_app` record that the unit and counit are identities on
  sections.

So the two notions agree in the strongest form. The underlying sheaves of abelian groups
and the morphisms are unchanged. The `𝒞^∞_X`-module structure of a module sheaf is
determined by its complex structure and recovered by the gluing of the II.2.5 Proposition.

## Provenance

The equivalence is the source Remark (base `T` clause). The source gives no proof beyond
the constants. The functors are built from published Library objects. The identity-on-sections
unit and counit and the fibre argument for `smul_toVector` are this file's own proof. The
generalization to arbitrary topological spaces costs nothing, because no step uses the t.d.
hypothesis. Worker 4 wrote this unit for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` (Task 1222), in agreement with Worker 1222.
