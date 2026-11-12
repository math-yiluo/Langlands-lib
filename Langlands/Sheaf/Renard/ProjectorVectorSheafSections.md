# Renard II.2.5: sections of the complex vector sheaf and original-vector sections

This companion to `ProjectorVectorSheaf` gives an explicit interface for the
sections of the complex vector sheaf `sheaf hX hM` attached to a nondegenerate
pointwise-test module. It then constructs the complex-linear core of Renard's
module-side comparison `M → ℳ_c(X)`, `m ↦ (χ_U · m)_U`. All declarations are in
`Langlands.Sheaf.Renard.ProjectorVectorSheaf`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
In the proof of the Theorem of II.2.5, printed p.39 / PDF p.45, the inverse
sheaf is `ℳ(U) = χ_U · M`, with restriction `m ↦ χ_U · m`. On printed p.40 /
PDF p.46 Renard computes
`ℳ_c(X) = ⋃_{U ∈ T_c} ℳ(U) = ⋃_U χ_U · M = M` for nondegenerate `M`.
This identification sends `m` to the compactly supported section whose value
on each compact open `U` is `χ_U · m`. The first proof paragraph, printed p.39
/ PDF p.45, notes that a section supported in a compact open `U` is fixed by
`χ_U`. These pages were read directly. The section API is an internal
interface to the imported construction. The comparison map is the literal
compact-open formula of the source. The source asserts that this map is
bijective, but this module neither proves nor assumes that.

## Section interface

Here `M : Type (max u v)` carries its original action and
`hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M`. By the imported
construction, a section of `(presheaf hX hM).obj (op V)` is definitionally a
published compatible family `BasisAllOpen.Families (rawPresheaf hX M) V`.

| Name | Content |
| --- | --- |
| `sectionMk hX hM V s hs` | The section with components `s U : Value hX M U.val` for every compact open `U ⊆ V`. `hs` is compatibility under the published projector `restrict`. `sectionMk_val` reads back the components (`rfl`). |
| `section_ext` | Two sections over `V` are equal when their components have equal underlying vectors in `M`. |
| `section_compatible` | The components of every section are compatible: `restrict hX M h (s.val U) = s.val W`. |
| `presheaf_map_val` | Restriction along `i : U ⟶ V` keeps exactly the components on compact opens inside `U`: `(((presheaf hX hM).map i.op).hom s).val W = s.val ⟨W.val, W.property.trans i.le⟩` (`rfl`). |
| `presheaf_map_smul` | Restriction is complex-linear. |
| `smul_val` | Complex scalars act on components through the canonical structure `originalModule hM` on `M` (`rfl`). |

Together with `sectionLinearEquiv` from `ProjectorVectorSheaf`, this exposes
the value on a compact open as the published fixed part of `χ_U`.

## Original-vector sections

| Name | Content |
| --- | --- |
| `originalFamily hX V m` | The compatible family with components `NonUnitalModuleCorner.projection (idempotent hX U) m`, that is `χ_U · m`. Compatibility is the published `action_absorb`: `χ_W χ_U = χ_W` for `W ⊆ U`. `originalFamily_val` gives the component `action hX M U m`. |
| `originalSection hX hM V` | The same as a complex-linear map `M →ₗ[ℂ] (presheaf hX hM).obj (op V)`, for the canonical complex structure on `M`. Additivity comes from additivity of the published action. Linearity is `action_smul_comm`: test actions commute with the canonical scalars. |
| `originalSection_val` | Component formula `χ_U · m` (`rfl`). |
| `originalSection_restrict` | Restricting `originalSection hX hM V m` along `U ⟶ V` gives `originalSection hX hM U m` (`rfl`). |
| `originalSection_of_value` | On a compact open `U`, a vector `s` of `χ_U · M` has original section equal to `sectionLinearEquiv hX hM U s` (`rfl`). |
| `sectionLinearEquiv_symm_originalSection` | On a compact open `U`, the component at `U` itself of the original section of `m` is the projection `χ_U · m` (`rfl`). |
| `sheafMap_originalSection` | Naturality: for an original intertwiner `f`, the sheaf map `sheafMap hX hM hN f` sends `originalSection hX hM V m` to `originalSection hX hN V (f m)`. The proof is `f.map_smul` at each characteristic test. |

## Compact support and the module-side comparison

The published `Langlands.Sheaf.CompactSupport` uses one universe for the
coefficient ring, the space and the sections. With coefficients `ℂ` this
universe is `Type`, so this section takes `X : Type` and `M N : Type` and uses
`presheaf.{0,0}` and `sheaf.{0,0}`. This size constraint is inherited from the
published interface.

| Name | Content |
| --- | --- |
| `exists_compactOpen_action_eq` | Every vector of a nondegenerate module is fixed by some compact-open test. If `e • m = m` for an idempotent `e`, then `K` is the compact clopen support of `e`. The published `characteristic_mul_eq_self_iff` gives `χ_K e = e`, hence `χ_K · m = m`. |
| `support_originalSection_subset` | If `χ_K · m = m`, the published `CompactSupport.support` of the global original section is contained in `K`. Take `x ∉ K` and the open `W = Kᶜ` (open because `K` is clopen). On each compact open `U ⊆ W`, `χ_U · m = χ_U χ_K · m = χ_{U ∩ K} · m`. This vanishes by the published `empty_value_eq_zero`, since `U ∩ K = ∅`. So the restriction to `W` is zero and the germ at `x` vanishes, by `TopCat.Presheaf.Γgerm_res_apply`. |
| `originalSection_mem_submodule` | The global original section lies in the published `CompactSupport.submodule`, because its support is closed and contained in a compact set. |
| `compactOriginal hX hM` | Renard's module-side comparison as a complex-linear map `M →ₗ[ℂ] CompactSupport.submodule (presheaf hX hM)`. It is the codomain restriction of `originalSection hX hM ⊤`. Its codomain is exactly the carrier of `(CompactSupport.functor ℂ (TopCat.of X)).obj (sheaf hX hM)`, as the interface `example` at the end checks. |
| `compactOriginal_val`, `compactOriginal_component` | Its underlying global section and its component `χ_U · m` on every compact open `U` (`rfl`). |
| `compactOriginal_naturality` | `CompactSupport.map (presheafMap hX hM hN f) (compactOriginal hX hM m) = compactOriginal hX hN (f m)` for every original intertwiner `f`. |

## Scope

Only definitions and intrinsic construction laws appear here. The module does
not prove or assume any of the following:

- that `compactOriginal` is injective, surjective or an isomorphism;
- that it intertwines the test-algebra action on compact sections;
- any statement of the II.2.5 Theorem.

The test-algebra structure on compact sections and the resulting comparison
morphism of nondegenerate modules belong to the compact-section functor of
Task 5338, Unit 1, which is a separate unit. So do the sheaf-side comparison
and the stalk descriptions.
