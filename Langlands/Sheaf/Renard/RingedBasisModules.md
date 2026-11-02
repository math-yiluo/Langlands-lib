# Renard II.2.3: actual module sheaves on a chosen ringed basis

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.3 “Faisceau de modules”,
printed p.38 / PDF p.44. Its registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.44–45 were read and the definition on PDF p.44 visually checked.
The separately registered 2010-edition corrections, source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, concern later sheafification and nondegenerate-module conventions;
they do not change this definition.

Renard starts with a ring sheaf on a chosen basis, gives the original section
groups left module structures over its rings of sections, and requires
restriction maps to be linear after restriction of scalars along the ring
restriction. `RingSheafCondition S` is literally the published
`SheafCondition (S ⋙ forget₂ RingCat AddCommGrpCat)`.
`RingedBasis B` carries the actual ring presheaf and this proof. The coefficient
rings are unital and may be noncommutative.

`BasisModuleSheaf S` is the actual full subcategory of Mathlib's
`PresheafOfModules S` defined by `SheafCondition M.presheaf`.
This category can be formed for any ring presheaf; its source interpretation
over a genuine ring sheaf is `RingedBasis.ModuleSheaf`.
The latter takes a `RingedBasis`, retaining its ring-sheaf proof explicitly.
The space universe `u`, scalar-carrier universe `r` and module-carrier
universe `v` are independent.

`BasisModuleSheaf.sections M U` is exactly `M.obj.obj (op U)`.
`restrict` is the original `PresheafOfModules.restrictₛₗ` on the opposite
inclusion, and `ringRestriction` is the original ring-presheaf map.
`restrict_apply`, `underlying_sections` and `underlying_restriction`
expose the unchanged carriers and values. `restrict_smul` gives the literal
equation `restrict (a • m) = ringRestriction a • restrict m`.
`isNormalized` applies the published `SheafCondition.isNormalized`;
there is no separate normalization field. `empty_section_eq_zero` is
its consequence on every empty basis object.

Morphisms are the actual Mathlib module-presheaf morphisms, wrapped only
by the full subcategory. `app` exposes their original linear components.
`app_restrict`, `id_app`, `comp_app` and `hom_ext` give the pointwise
restriction, identity, composition and extensionality laws.
`PreservesScalars` is an explicit condition on an additive natural
transformation. `homMk` consumes that proof and uses Mathlib's
`PresheafOfModules.homMk`. `homEquiv` identifies module-sheaf morphisms
with precisely the additive natural transformations satisfying this condition.
Its inverses are proved by componentwise extensionality. No arbitrary
additive transformation is assigned scalar linearity.

`moduleSheafInclusion` is the actual fully faithful full-subcategory
inclusion into `PresheafOfModules S`.
`moduleSheafToBasisSheaf` retains the original additive presheaf, derives
normalization from its sheaf proof, and keeps the same underlying natural
transformation on morphisms. It is faithful, using the faithfulness of
Mathlib's `toPresheaf`. No fullness assertion is made for this functor.
`moduleSheaf_forget_comparison` identifies its composite with the existing
`sheafForget` and `presheafInclusion` with inclusion followed by
Mathlib's `toPresheaf`.
`moduleSheafEvaluation` evaluates the original module presheaf in
`ModuleCat (S.obj (op U))`. Its object and morphism formulas, the underlying
sheaf formulas, and `moduleSheafEvaluation_forget` are definitional equalities.

The full-subcategory packaging, morphism correspondence, functors and
arbitrary-topological-space version are internal formal generalizations of
the definition in this chapter on totally disconnected spaces. They require
only the supplied topology and its actual chosen basis, with no separation,
compactness, size, intersection-closure or nonemptiness assumptions.
Empty spaces and empty basis objects are included. This unit defines objects
satisfying the sheaf axiom; it does not assert that every module presheaf
is a sheaf.

Worker 633 implemented this unit, reusing the published basis framework and
Mathlib module presheaves. Worker 6 contributed the source audit and the
actual-module-presheaf/full-subcategory interface design recorded in the task.
Construction from a basis sheaf with supplied module structures and the
remaining intrinsic gluing/all-open interfaces follow in a separate unit.
Locally constant scalars, their actions, restriction along constants,
basis-change equivalences and the II.2.5 equivalences retain separate successors.
