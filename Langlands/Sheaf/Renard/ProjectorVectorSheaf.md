# Renard II.2.5: the complex vector sheaf of a nondegenerate test module

This module constructs Renard's inverse functor in II.2.5 on the actual category
of sheaves of complex vector spaces. All declarations are in
`Langlands.Sheaf.Renard.ProjectorVectorSheaf`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
In the proof of the Theorem of II.2.5, printed p.39 / PDF p.45, Renard defines
the inverse functor: for a nondegenerate `𝒟(X)`-module `M` and a compact open
`U`, `ℳ(U) = χ_U · M`, with restriction `ρ_{V,U}(m) = χ_U · m` for compact
opens `U ⊂ V`. He notes `ℳ(U) = {m ∈ M | χ_U · m = m}` and proves the sheaf
property on the basis of compact opens (printed pp.39–40 / PDF pp.45–46).
Renard regards `ℳ` as a sheaf of `𝒞^∞_X`-modules. By the Remark before the
Theorem (printed p.39 / PDF p.45), such sheaves are equivalent to sheaves of
complex vector spaces, and for compact-open-basis sheaves by the last
paragraph of II.2.1. These pages were read directly.

The published additive construction is
`ProjectorBasisSheaf.nondegenerateFunctor`: its value on a compact open is the
fixed subgroup `Value hX M U` of the characteristic test `χ_U`, and its
restriction is the projector. The published `BasisMathlib.toMathlib`
extends basis sheaves to actual Mathlib sheaves of abelian groups through
compatible families. This module adds only the complex structure. The source
leaves it implicit: a `𝒟(X)`-module is a complex vector space, and
`χ_U · M` is a complex subspace. Here the complex structure is the published
canonical one, `NondegenerateScalars.complexModule`, with
`c • m = (c • e) • m` for every idempotent `e` fixing `m`. It is
characterized by `NondegenerateScalars.module_eq_of_compatible`. The module
reads no complex scalar action from elsewhere. Everything else is an internal
elaboration of the cited construction, which reuses the published objects by
Lean name.

## Hypotheses and size constraint

`X : Type u` carries its supplied topology. The hypothesis
`hX : Langlands.Topology.IsLocallyProfinite X` is the published Renard II.1.1
condition: Hausdorff with a compact open neighbourhood basis. The section
`Values` works for an original module `M : Type v` with any universe `v`. The
families, the sheaf and the functor use carriers in `Type (max u v)`. This is
forced by the published `BasisMathlib.toMathlib.{u,v}`, whose compatible
families indexed by basis opens of `X` lie in `max u v`. It is the same
documented size convention as that module, not a resizing claim. In particular
`functor.{0,0}` lands in `TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X)` for
`X : Type`. This is the universe instance needed by the published
`Langlands.Sheaf.CompactSupport`, whose coefficient, base and section
universes coincide. The interface examples at the end check `functor.{u,v}`,
`functor.{0,0}` and `functor.{1,2}`.

## Complex structure on projector ranges

For `hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M`:

| Name | Content |
| --- | --- |
| `originalModule hM` | The canonical complex structure `NondegenerateScalars.complexModule PointwiseTestAlgebra.isIdempotented hM` on `M`. It is a definition, not an instance, because it depends on the proposition `hM`. |
| `action_smul_comm` | `a • (c • m) = c • (a • m)` for every test function `a` and `c : ℂ`. This combines the published `action_smul` and `smul_action`. |
| `smul_mem_value` | `χ_U · M` is stable under complex scalars: `χ_U • (c • s) = c • χ_U • s = c • s`. |
| `valueModule hX hM U` | The complex structure on `Value hX M U = χ_U · M`. It is pulled back along the published inclusion by `Function.Injective.module`, with `(c • s).val = c • s.val` (`valueModule_smul_val`, by `rfl`). |
| `restrict_smul` | The published projector restriction `restrict hX M h` is complex-linear. |

## The complex vector sheaf

Here `M : Type (max u v)`.

| Name | Content |
| --- | --- |
| `familySMul`, `familySMul_val` | Componentwise complex scalars on the published compatible families `BasisAllOpen.Families (rawPresheaf hX M) V`. Compatibility is preserved by `restrict_smul`. |
| `familyModule hX hM V` | The resulting `Module ℂ` structure. It is pulled back from the product of the `valueModule` structures along the published subgroup inclusion. |
| `familySpace hX hM V` | The bundled `ModuleCat.{max u v} ℂ` object on the original family carrier. |
| `familyRestrictionLinear` | The published `BasisAllOpen.familyRestriction`, discarding components outside the smaller open, as a complex-linear map. |
| `presheaf hX hM` | The actual `TopCat.Presheaf (ModuleCat.{max u v} ℂ) (TopCat.of X)` with these values and restrictions. |
| `presheaf_forget₂` | `presheaf hX hM ⋙ forget₂ (ModuleCat ℂ) AddCommGrpCat` is definitionally the underlying presheaf of the published `(BasisMathlib.toMathlib (compactOpenBasis hX)).obj (basisSheaf hX M)` (`rfl`). |
| `isSheaf` | The sheaf condition. It is transported from the published Mathlib sheaf by `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'` along `forget₂`. That functor reflects isomorphisms and preserves limits, using `ModuleCat.hasLimitsOfSize.{u,u,max u v,0}`. No gluing argument is repeated. |
| `sheaf hX hM` | The actual object of `TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X)`. |
| `sectionLinearEquiv hX hM U` | For a compact open `U`, a complex-linear equivalence `Value hX M U ≃ₗ[ℂ] (presheaf hX hM).obj (op U.obj)`: Renard's `ℳ(U) = χ_U · M`. Its underlying additive equivalence is exactly the published `BasisMathlib.basisSectionIso` (`sectionLinearEquiv_toAddEquiv`, by `rfl`). Its components are `s ↦ (W ↦ restrict hX M W.property s)`, and its inverse reads the component at `U` itself (`sectionLinearEquiv_apply`, `sectionLinearEquiv_symm_apply`). |

## Morphisms and the functor

For nondegenerate `M N P : Type (max u v)` and an original intertwiner
`f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N`:

| Name | Content |
| --- | --- |
| `familyLinearMap hX hM hN f V` | The published componentwise map `BasisAllOpen.familyMap (rawMap hX f) V` as a complex-linear map `familySpace hX hM V ⟶ familySpace hX hN V`. Linearity is the published `NondegenerateScalars.map_smul`: original additive intertwiners preserve the canonical scalars. `familyLinearMap_val` gives the component formula `f (s.val U).val`. |
| `presheafMap`, `sheafMap` | The natural transformation with these components, and the corresponding sheaf morphism `ObjectProperty.homMk (presheafMap …)`. `sheafMap_app_val` gives the same component formula. |
| `sheafMap_id`, `sheafMap_comp` | Identity and composition laws, by extensionality and `rfl` on components. |
| `functor hX` | The actual functor `NondegenerateModuleCat.{u, max u v} (PointwiseTestAlgebra.Carrier X) ⥤ TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X)`. Its object is `sheaf hX M.property` and its map is `sheafMap … f.hom` (`functor_obj`, `functor_map`). |
| `functor_comp_forget₂` | `functor hX ⋙ sheafCompose _ (forget₂ (ModuleCat ℂ) AddCommGrpCat)` equals `nondegenerateFunctor hX ⋙ BasisMathlib.toMathlib (compactOpenBasis hX)`, by `rfl`. Thus this functor refines the published additive inverse functor exactly. |

## Scope

The module does not prove that the functor is an equivalence, fully faithful
or essentially surjective. It assumes no comparison isomorphism and no inverse
law. It does not construct compact sections, the locally constant scalar
action on sheaf sections, the comparison maps of the II.2.5 Theorem or stalk
descriptions; those are separate constructions and statements. Empty opens
need no special treatment here: the published `empty_value_eq_zero` makes the
value on the empty compact open zero. The source's assertion that constants
inject into every scalar section ring fails for the empty open. That
correction concerns the locally constant scalar sheaf, which this module does
not use.
