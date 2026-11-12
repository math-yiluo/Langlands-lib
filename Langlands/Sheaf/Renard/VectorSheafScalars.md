# Locally constant scalars on complex vector sheaves

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5 Proposition and its proof,
printed pp.38–39 / PDF pp.44–45, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Proposition says that a sheaf `M` of complex vector spaces on a t.d.
space is naturally a sheaf of `C^∞_X`-modules: for a section `s` over `U`
and a locally constant function `f` on `U`, the section is
`x ↦ f(x) s(x)` in the étalé space.

## Objects

`VectorSheaf X` is Mathlib's `TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)`
for `X : Type u`: sheaves of complex vector spaces on all opens of `X`.
This is the category used by the consumer modules
`Langlands.Sheaf.Renard.SectionActions` and by
`Langlands.Sheaf.CompactSupport`. The source states the Proposition for
sheaves on the base of compact opens; by the last paragraph of II.2.1 these
are equivalent to sheaves on all opens, and the code works directly with
all opens. The construction needs no hypothesis on the topology of `X`.

Mathlib provides preservation of filtered colimits by the forgetful functor
of `ModuleCat.{u} R` only for `R : Type u`. The two instances
`forget₂_preservesFilteredColimits` and `forget_preservesFilteredColimits`
supply it for `ℂ : Type` at every carrier universe `u`, from Mathlib's
explicit filtered-colimit cocones of modules and of abelian groups. They are
used only so that Mathlib's elementwise stalk and germ lemmas apply.

## The action

For `f : LocallyConstant U ℂ` and `x ∈ U`, `fiber f x` is the open subset of
`U` where `f` takes the value `f x`. The fibres cover `U`. On each fibre,
`fiberSection` is the constant multiple `f x • s|fiber`; these are
compatible because two fibres are either equal or disjoint, which the code
checks on germs. `smul F f s` is the unique glued section from
`TopCat.Sheaf.existsUnique_gluing'`, and `restrict_smul_fiber` records its
defining property.

`germ_smul` (and its simp form `germ_lc_smul` for the instance) is the
source formula `(f s)(x) = f(x) s(x)`, read in Mathlib's colimit stalk.
`ext_germ` is Mathlib's `TopCat.Presheaf.section_ext`, and `eq_smul_iff`
characterizes `f • s` as the unique section satisfying the germ formula.
All module laws of `module`, the instance
`Module (LocallyConstant U ℂ) (F.presheaf.obj (op U))`, are proved by
comparing germs after `germ_smul`.

## Compatibility laws

- `restrict_smul_of_eq`: on an open `V ≤ U` where `f` is constant `c`,
  the restriction of `f • s` is `c` times the restriction of `s`.
- `constants_smul` and `algebraMap_smul`: the constant function
  `LocallyConstantScalar.constants ℂ U c` (equivalently Mathlib's algebra
  map) acts by the original complex scalar `c`. This holds for every open,
  including the empty open, where the published constants map is not
  injective (see `LocallyConstantScalarConstants`). The source's remark that
  constants inject into every section ring is therefore not used.
- `isScalarTower` and `smulCommClass`: the new action is compatible with the
  original complex structure.
- `restrict_smul` and `restrictSemilinear`: restriction from `V` to `U ≤ V`
  is semilinear along the published ring restriction
  `LocallyConstantScalar.restrict ℂ h`. This is the source's requirement
  (II.2.3) that restriction maps are module maps after restriction of
  scalars.
- `app_smul` and `appLinear`: every morphism of complex vector sheaves is
  linear over the locally constant scalars on each open, proved with
  Mathlib's stalk functor.

This file constructs the action and its laws only. It does not package the
action as a sheaf of modules over a ringed space, and it constructs no
compact-section module, test-algebra action or categorical equivalence.
Those are in `CompactSectionTestModule` and later units.

Worker 184 implements this unit for Task 5338.
