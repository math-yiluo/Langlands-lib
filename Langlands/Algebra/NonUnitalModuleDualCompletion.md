# The full dual and the completion of the nondegenerate dual

Worker 734 constructed this pair. It uses David Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026. The
governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The pair implements the two maps of I.4.3, "Dualité et complétion",
printed page 25 / PDF page 31. The conventions it relies on were also
read: I.1.1–I.1.5, printed pages 5–11 / PDF pages 11–17 (idempotented
algebras, nondegenerate modules, the order on idempotents and the
completion), recovered complex scalars in I.2.1, printed page 14 / PDF
page 20, and the dual in I.4.1, printed pages 22–23 / PDF pages 28–29.
The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was read. It has no correction to the completion of the
dual. The 2026 edition governs.

All declarations below are in
`Langlands.Algebra.NonUnitalModuleDualCompletion`.

## The source passage

Let `A` be a complex idempotented algebra and `M` a nondegenerate
`A`-module. Renard defined `M~` as the nondegenerate part of `M*`. I.4.3
opens with: "Il est facile de voir directement que lorsqu'on complète
`M~`, on retrouve `M*`." He then proves this formally. He uses a chain of
Hom isomorphisms for every right module `N`, through the adjunction
I.1.5, (I.2.2.6) and (I.2.2.3), and the isomorphism
`ι : N_A ⊗_A M → N ⊗_A M`. Yoneda (A.III.3) then gives the conclusion
`completion(M~) = completion((M*)_A) ≃ M*`.

This pair takes the direct route that the opening sentence calls easy.
It writes down the two actual maps between `M*` and the actual
compatible families of actual vectors of `M~`, and proves their
intrinsic laws. The Hom chain, the map `ι` and its inverse `Φ`, and the
Yoneda step are **not** formalized here. Nor is it proved that the two
maps are inverse to each other.

## Carriers, actions and universes

Right `A`-modules are left `Aᵐᵒᵖ`-modules, as in the published dual. The
three carriers are the published ones:

- `F = NonUnitalModuleDual.FullDual hA hM`, the actual
  `Module.Dual ℂ M`. `M` carries exactly
  `NondegenerateScalars.complexModule hA hM`. No complex module on the
  original `M` is assumed.
- `D = NonUnitalModuleDual.Dual hA hM`, the nondegenerate part of `F`
  for `hA.op`.
- `C = NonUnitalModuleLeftLimit Aᵐᵒᵖ D`. A vector `x` of `C` is an actual
  family `e ↦ x.val e : D` indexed by `Idempotent Aᵐᵒᵖ`. It satisfies
  fixation `e • x.val e = x.val e` and coherence
  `e • x.val f = x.val e` whenever `e ≤ f`.

The actions are the named published ones. On `F` this is
`NonUnitalModuleDual.fullAction hA hM`, with
`(a • φ) m = φ (a.unop • m)`. On `D` it is
`NonUnitalModuleDual.dualAction hA hM`. Both are installed only as local
instances in this file. On `C` the action is always written explicitly
as the original family action
`NonUnitalModuleLeftLimit.nonUnitalModule hA.op`. Its published
coordinate formula `NonUnitalModuleLeftLimit.smul_val` reads
`(a • x).val e = (e * a) • x.val f` for every right local unit `f` of
`e * a`.

`completion_eq_functor_obj` and `completion_functor_obj_action` are
`rfl` equations. They identify `C` and its action with the published
completion functor's object at the nondegenerate module `D`. `F` and
`D` live in `Type uM`. `C` lives in `Type (max uA uM)`, because its
families are indexed by the idempotents of `Aᵐᵒᵖ`.

The private lemma `exists_rightUnit` extracts a right local unit from
`IsIdempotented.iff_two_sided_local_units`. Indices are translated with
the published `NonUnitalModuleDualFixedPartMaps.oppositeIdempotent`,
whose value is `op e`. No second helper with the same meaning is
introduced. `oppositeIdempotent_le` proves that it preserves Renard's
order. The two order equations `f e = e` and `e f = e` simply exchange
roles under `op`.

## The complex module on the completion

`completionModule hA hM` is a `Module ℂ C` on the existing additive
group of `C`. Its scalar operation is pointwise,
`(c • x).val e = c • x.val e`, using exactly
`NonUnitalModuleDual.dualModule hA hM` on `D`. The scaled family is
again fixed and coherent: `c` commutes with the action of `e` on `D`
by `NonUnitalModuleDual.dual_smulCommClass`. The module axioms hold
coordinatewise.

The scalar formulas are all definitional. `completionModule_smul_coe`
gives the entire scaled family and `completionModule_smul_val` its
coordinates. `completionModule_smul_functional` gives the entire
included full-dual functional `((c • x).val e).val = c • (x.val e).val`,
and `completionModule_smul_apply` its values.

`completion_isScalarTower` and `completion_smulCommClass` prove
`IsScalarTower ℂ Aᵐᵒᵖ C` and `SMulCommClass ℂ Aᵐᵒᵖ C` for the unchanged
family action. At a coordinate `e`, choose a right local unit `f` of
`e * a`. The same `f` is a right local unit of `e * (c • a)`, by
`mul_smul_comm` and `smul_mul_assoc`. Both sides are therefore computed
by `smul_val` at the same `f`. The tower then follows from
`NonUnitalModuleDual.dual_isScalarTower` and the commutation from
`dual_smulCommClass` on `D`. No nondegeneracy of `C` is assumed or
asserted.

## The forward map `F → C`

`forwardCoordinate hA hM e φ` is the full functional `(e : Aᵐᵒᵖ) • φ`,
viewed in `D`. The membership witness is `e` itself, via
`e • (e • φ) = (e * e) • φ = e • φ`. `forwardCoordinate_eq` exposes this
entire subtype element with its proof. `forwardCoordinate_fixed` proves
coordinate fixation from idempotence. `forwardCoordinate_coherent`
proves coherence from `e * f = e` for `e ≤ f`.

`toCompletion hA hM φ` is the family `e ↦ forwardCoordinate hA hM e φ`.
Its coordinate formulas are definitional:

- `toCompletion_val`: the coordinate is `forwardCoordinate hA hM e φ`;
- `toCompletion_functional`: the whole coordinate functional is
  `(e : Aᵐᵒᵖ) • φ`;
- `toCompletion_coe`: the whole function is
  `fun m => φ (e.val.unop • m)`, using the published full action;
- `toCompletion_apply`: its value at `m` is `φ (e.val.unop • m)`.

`toCompletion_fixed` and `toCompletion_coherent` restate the
compatible-family conditions of the image.

`toCompletion_zero` and `toCompletion_add` follow coordinatewise from
`smul_zero` and `smul_add` for the full action.
`toCompletion_complex_smul` uses
`NonUnitalModuleDual.full_smulCommClass`. `toCompletion_action` is the
right-action equivariance. At a coordinate `e`, choose a right local
unit `f` of `e * a`. Then `smul_val` gives
`(a • toCompletion φ).val e = (e * a) • (f • φ)`. This equals
`((e * a) * f) • φ = (e * a) • φ = e • (a • φ)` by `mul_smul` for the
full action.

The packages are `toCompletionAddHom` (`F →+ C`), `toCompletionLinear`
(`F →ₗ[ℂ] C` for `completionModule`), and `toCompletionHom`. The last
is a `NonUnitalModuleHom Aᵐᵒᵖ` whose type names `fullAction hA hM` and
`NonUnitalModuleLeftLimit.nonUnitalModule hA.op` explicitly.
`toCompletionLinear_toAddMonoidHom` and `toCompletionHom_toAddMonoidHom`
identify the entire underlying additive maps of both packages with
`toCompletionAddHom`, by `rfl`. The coercion lemmas
`toCompletionAddHom_apply`, `toCompletionLinear_coe` and
`toCompletionHom_apply` say the same for the functions.

## The reverse map `C → F`

For `x : C` and `m : M`, the value is
`(x.val (oppositeIdempotent e)).val m` for any `e : Idempotent A` with
`(e : A) • m = m`.

*Choice independence.* `coordinate_apply_eq_of_le` handles `e ≤ f` with
`e` fixing `m`. Coherence of `x` at
`oppositeIdempotent e ≤ oppositeIdempotent f` gives
`x(op e) = op e • x(op f)`. Evaluating at `m` with the dual action
gives `x(op f) (e • m) = x(op f) m`. `coordinate_apply_independent`
treats two arbitrary fixers `e` and `f` of `m`. It takes a common upper
bound `g` of `{e, f}` from `IsIdempotented.finite_upper_bound` and
applies the previous lemma to `e ≤ g` and `f ≤ g`. This parallels
Renard's own well-definedness check for `φ(n, m) = (n · e) ⊗ m` in
I.4.3, which also passes through a common idempotent `h`.

*The functional.* The private `fullValue` uses the fixer `(hM m).choose`.
The private `fullValue_eq` proves the value equals the formula at every
fixer. `toFullDual hA hM x` is the actual `ℂ`-linear functional on `M`
with the recovered `complexModule`. For additivity, the private
`exists_common_fixer` gives one idempotent `g` fixing both `m` and `n`:
an upper bound of their fixers, via `Idempotent.smul_eq_of_le`. Then `g`
fixes `m + n`, and additivity of the single functional `x(op g)`
applies. For complex homogeneity, `fixer_complex_smul` shows that any
fixer `e` of `m` also fixes `c • m`. The original action commutes with
recovered scalars by `NondegenerateScalars.action_smul` and
`NondegenerateScalars.smul_action`. Then `ℂ`-linearity of `x(op e)`
applies.

*Every-fixer formula.* `toFullDual_apply` states
`toFullDual hA hM x m = (x.val (oppositeIdempotent e)).val m` for every
`e` with `(e : A) • m = m`. This is the public evaluation formula. The
choice is confined to the private `fullValue`, and no public statement
mentions it.

*Laws in `x`.* `toFullDual_zero`, `toFullDual_add` and
`toFullDual_complex_smul` (for `completionModule`) use linear-map
extensionality. At each `m` they choose one fixer and apply the
every-fixer formula to all terms. The pointwise operations on `C` and
`D` then close the goal definitionally.

*Equivariance.* `toFullDual_action` proves
`toFullDual (a • x) = a • toFullDual x` for the family action and the
full action. Given `m`, choose a fixer `e₀` of `m`. Choose a two-sided
local unit `h` of `{a.unop, e₀}` directly from `hA`. Then
`h * a.unop = a.unop`, `e₀ ≤ h` so `h` fixes `m`, and
`h • (a.unop • m) = a.unop • m`. Under `op`, `oppositeIdempotent h` is a
right local unit of `oppositeIdempotent h * a`. So `smul_val` evaluates
`(a • x)` at `op h` as `(op h * a) • x(op h)`. At `m` this is
`x(op h) ((a.unop * h) • m) = x(op h) (a.unop • m)`. Because `h` fixes
`a.unop • m`, the every-fixer formula identifies it with
`toFullDual x (a.unop • m) = (a • toFullDual x) m`. Renard's balancing
argument in the same section chooses the same kind of local unit
(`h · m = m`, `a h = a`, `h a = a`).

*Packages.* `toFullDualAddHom` (`C →+ F`), `toFullDualLinear`
(`C →ₗ[ℂ] F` for `completionModule`) and `toFullDualHom` (a
`NonUnitalModuleHom Aᵐᵒᵖ` from the family action to `fullAction hA hM`)
package the reverse map. `toFullDualLinear_toAddMonoidHom` and
`toFullDualHom_toAddMonoidHom` identify both underlying additive maps
with `toFullDualAddHom` by `rfl`. `toFullDualAddHom_apply`,
`toFullDualLinear_coe` and `toFullDualHom_apply` state this for the
functions.

## Interface checks and zero cases

The file ends with `example`s assigning complete unapplied
declarations to fully quantified types. The binders are
`{A : Type uA} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
[SMulCommClass ℂ A A] {M : Type uM} [AddCommGroup M]
[NonUnitalModule A M] (hA) (hM)`. The same 45 checks are repeated at
independent universes `uA`, `uM` and at `(uA, uM) = (0, 1)` and
`(1, 0)`. They cover:

- the scalar module and its four formulas, and the tower and
  commutation laws;
- `forwardCoordinate`, `toCompletion` and all its coordinate and
  algebraic laws, and the three forward packages with their additive
  identifications and coercions;
- `coordinate_apply_eq_of_le`, `coordinate_apply_independent`,
  `fixer_complex_smul`, `toFullDual`, `toFullDual_apply`, its algebraic
  and equivariance laws, and the three reverse packages with their
  additive identifications and coercions.

Every check states its formula on the original carriers `F`, `D` and
`C`, with the original scalar modules and named actions. No replacement
model or transport is used.

The `ZeroCases` section covers two degenerate cases. The first is the
zero carrier `PUnit` over an arbitrary idempotented algebra with
`NonUnitalModule.zero`; it is nondegenerate with the zero idempotent as
fixer. Both intertwiner packages instantiate there, and `toFullDual` is
zero. The second is the zero algebra `PUnit` with
`IsIdempotented.of_ring`. Arbitrary dimension and the zero idempotent
are allowed throughout. No finiteness or unit hypotheses are added.

## Scope

This unit stops at the two actual maps and their intrinsic laws. Not
stated or proved here, and left to separate successors:

- the inverse identities, bijectivity, and additive or linear
  equivalences;
- naturality in `M` and any categorical natural isomorphism;
- the source's Hom chain;
- the tensor-smoothing isomorphism `ι`;
- formula (I.4.3.1).

No inverse or naturality conclusion is assumed as an input.
