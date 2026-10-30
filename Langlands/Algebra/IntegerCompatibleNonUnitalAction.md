# Canonical integer compatibility of additive nonunital actions

This module reuses the published `CompatibleNonUnitalAction` conversions and
adds the automatic integer specialization for the original additive actions
and morphisms.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 prepared the original Lean and Markdown draft. Worker 691 independently
checked the implementation and read the conventions on printed pages 5–6 / PDF pages 11–12
and I.2.1 on printed page 14 / PDF page 20 directly for this unit.
The 2026 original governs. The complete I.2.2 context on PDF page 21
and supplementary 2010-edition errata PDF pages 1–3 and 18–19 were also read;
this is a limited supplementary check. No dedicated project errata path
was present in the workspace, project notes or pinned Library.

Every declaration here is derived implementation content. An additive
action has canonical integer compatibility, and an additive morphism
preserves integer scalar multiplication. This supplies the existing
generic interfaces with integer scalars without imposing complex
linearity. Renard I.2.1 distinguishes additive module morphisms from
their complex-linear intersection for general nonunital actions.
This unit does not identify those Hom spaces or settle any source
finite-generation or Noetherian convention.

The acting ring `A : Type uA` is an arbitrary `NonUnitalRing`, and the
carriers `V : Type uV`, `W : Type uW` and composition target
`P : Type uP` are arbitrary additive commutative groups. These universes
are independent. Every integer scalar structure is the canonical
`AddCommGroup.toIntModule` of the corresponding additive group.
There is no commutativity, unit law, nondegeneracy, nontriviality,
finite generation, dimension or coefficient-field hypothesis.
In particular, if `A = ℤ` and the original action is zero, the canonical
integer scalar multiplication on the carriers remains the one determined
by their additive groups. The original action and the scalar action are
separate inputs to the compatible interface.

In `Langlands.Algebra.NonUnitalModule`, `int_isScalarTower` proves the
missing tower law for the original nonunital action. For fixed `v`,
the map `a ↦ a • v` is an additive homomorphism, so its `map_zsmul`
law gives `(n • a) • v = n • (a • v)`. Mathlib already supplies
the commuting integer-scalar action. The named tower proof is not
registered as an instance.

`toIntLinearEndHom` selects that proof locally and uses the published
`toLinearEndHom ℤ`. Its application is exactly the original action.
The two round trips reuse the published `ofLinearEndHom` and prove
equality of the original action structures and actual homomorphisms,
respectively, by extensionality and reflexivity.
`equivIntLinearEndHom` packages these maps and their round trips.
`toIntLinearEndHom_zero` proves that the original zero action remains
the zero homomorphism, even when the acting ring is unital.

In `Langlands.Algebra.NonUnitalModuleHom`, `toIntLinearIntertwiner`
uses the published generic `toLinearIntertwiner ℤ`, with integer
linearity supplied by the original additive map's `map_zsmul`.
Its application is the original function, and its underlying
linear map is definitionally `f.toAddMonoidHom.toIntLinearMap`.
`equivIntLinearIntertwiner` packages it with the existing
`ofLinearIntertwiner`, selecting only the local integer tower proofs.
Its inverse evaluation and both round trips are reflexive.
The identity and composition laws are also reflexive equalities of
the actual bundled intertwiners.

This file provides definitions and intrinsic construction laws. It
introduces no global action or scalar instances. Localization,
unitization, categories, submodule correspondences and all finiteness
and stability statements remain separate units.
