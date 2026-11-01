# Original nonunital scalar restriction

This internal prerequisite for Renard I.2.3 pulls back actual additive
nonunital actions along an actual nonunital ring homomorphism. It retains
the given additive group and the specified original action. It assumes no
unit-action law, even if the scalar rings have units. Both scalar-ring
universes and every unbundled vector-carrier universe are independent.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.2, printed pp.5–8/PDF11–14, define the
original actions and nondegenerate modules. I.2.3 printed p.16/PDF22
starts with unital complex-algebra restriction, then distinguishes the
general commuting-bimodule setup and warns that a morphism alone does not
make the restricted regular module nondegenerate. Printed p.18/PDF24
spells out the two-sided finite-family local-unit hypothesis.

The all-ring ambient construction here is a general internal prerequisite
specializing to the source, rather than an assertion that arbitrary scalar
morphisms give a functor between its nondegenerate categories.

## The actual ambient construction

All names below are in
`Langlands.Algebra.NonUnitalModuleRestrictScalars`. For independent
nonunital rings `A`, `B` and an additive commutative group `M`,
`module φ hM` composes the *specified* original action representation
`NonUnitalModule.toEndHom hM` with `φ : A →ₙ+* B`, then applies the
published `NonUnitalModule.ofEndHom`. Thus its action is precisely
`a • m = φ(a) • m`, with the right side using `hM`. The equations
`toEndHom_module` and `module_action` retain the complete representation
and its action formula; `module_smul` states the same formula for the
scalar-multiplication operations themselves, with both action structures
supplied explicitly. All three hold definitionally. No integer unitization or replacement carrier is
used. `module_id` and `module_comp` give equality of the actual action
structures. The identity proof eliminates the original structure; the
composition proof is definitional. `module_zero` preserves the original
zero action. `module_zeroHom` identifies restriction by the zero scalar
homomorphism with the zero action: injectivity of the published
endomorphism-representation equivalence reduces this to the original
`zero_smul` law.

`map φ f` retains the entire additive homomorphism of the original
intertwiner `f`. Its only extra obligation is the original intertwining
law evaluated at `φ(a)`. The whole additive-map equality
`map_toAddMonoidHom`, whole-function equality `coe_map`, and application
formula `map_apply` specify this retention. The laws `map_id`,
`map_comp`, `map_zero`, `map_add`, and `map_neg` follow by extensionality
and the pointwise formulas. `mapAddHom` bundles this operation as an
additive homomorphism between the published pointwise Hom groups;
`mapAddHom_apply` and `coe_mapAddHom` identify its actual function.
Source and target vector universes are independent of one another and of
both scalar-ring universes.

`functor φ` sends an actual object of `NonUnitalModuleCat B` to the
same additive carrier with action `module φ M.isModule`. It sends each
morphism to `map φ f`, so the preceding identity and composition laws
supply its functor laws. The equations `functor_obj_carrier`,
`functor_obj_module`, `functor_obj_addCommGroup`, and
`functor_map_toAddMonoidHom` specify the actual object, additive
structure, action, and entire underlying morphism. Its `Additive`
instance uses `map_add`. Both categories use the same vector-carrier
universe, which remains independent of both scalar-ring universes.

## Nondegenerate restriction and its input

`HasLeftLocalUnits φ : Prop` means that for every `b : B` there is an
actual idempotent `e` of `A` with `φ(e) * b = b`. This is the elementwise
nondegeneracy condition for the pulled-back *left* regular action on
`B`. It is a sufficient input to the present construction; it does not
assert the book's two-sided bimodule hypothesis. The separately named
`HasTwoSidedLocalUnits φ : Prop` spells out the source condition: each
finite subset of `B` has a common idempotent `e` of `A` such that both
`φ(e) * b = b` and `b * φ(e) = b` hold throughout the subset.
`HasTwoSidedLocalUnits.hasLeftLocalUnits` specializes it to a singleton
and takes the left equality. Neither predicate assumes a unit, an
idempotented source or target ring, or nontriviality. The source quantifies
over finite families `b₁, …, bₙ`; a family satisfies the condition exactly
when its finite set of values does, so quantifying over `Finset B` states
the same condition.

For a unital ring homomorphism `φ`,
`hasLeftLocalUnits_of_ringHom` supplies this sufficient condition with
`e = 1`, using `φ(1) = 1`. This does not impose a unit-action law on
arbitrary ambient modules. Its use to restrict a nondegenerate module
still requires that module's own nondegeneracy premise. (For a unital ring
`R`, the published `isNondegenerate_iff_isUnitalModule` identifies
nondegenerate ambient `R`-modules with those whose action satisfies
`1 • m = m`; this module neither uses nor restates that fact.)

The intrinsic preservation lemma `isNondegenerate` is what makes the
full-subcategory construction well typed. Given a vector `m`, choose an
idempotent `b` of `B` fixing it, then choose an idempotent `e` of `A`
with `φ(e) * b = b`. Associativity gives
`φ(e) • m = φ(e) • (b • m) = (φ(e) * b) • m = m`.
This argument uses only the stated left-local-unit condition and the
original action laws. `nondegenerateFunctor φ hφ` uses the same ambient
objects and maps and this proof of their property. Its laws are those of
`map`, lifted through the full-subcategory Hom wrapper; it is additive
by the same pointwise addition law.
`nondegenerateFunctor_obj` and `nondegenerateFunctor_map_hom` specify
its underlying object and complete ambient map, and
`nondegenerateFunctor_map_toAddMonoidHom` states that the entire original
additive map is retained. The equality
`nondegenerateFunctor_comp_inclusion` of entire composed functors
identifies its ambient restriction with `functor φ` after the actual
inclusions.

Two checked adapters build the nondegenerate functor from the other
inputs: from a proof of the source's `HasTwoSidedLocalUnits φ`, via
`HasTwoSidedLocalUnits.hasLeftLocalUnits`; and from a unital ring
homomorphism `φ : R →+* S`, as
`nondegenerateFunctor φ.toNonUnitalRingHom (hasLeftLocalUnits_of_ringHom φ)`.

## Checks and limits

The module contains complete unapplied declaration checks for `module`,
`map`, `mapAddHom`, both functors, both additive instances, and both
local-unit predicates at arbitrary independent universes. Fixed unequal
specializations of `module`, `map`, `mapAddHom` and both functors put the
vector universe above both scalar universes and below both; the Hom checks
also separate source and target vector universes. Explicit competing-action
checks select original structures independently, including `A = B = M`
and two different actions on the same vector carrier: they cover the
representation formula, the scalar-multiplication formula `module_smul`,
the action of a functor object built from an explicitly chosen structure,
and the retained additive maps. Where two actions share a type, the
projections and structure arguments are supplied explicitly rather than
relying on local instance selection.

Zero actions on nonzero groups are retained: restriction of the zero
action on `ℤ` still has `1 • 1 = 0`, even in the presence of a competing
action, and so does the object of `functor` built from the zero action on
`ℤ`. A checked example starts with the usual action of `ℤ` on itself,
proves it nondegenerate using the idempotent `1`, and shows that restriction
along the zero homomorphism is not nondegenerate by applying the alleged
property to `1`. Another example shows that this zero homomorphism fails
`HasLeftLocalUnits`, again at `1`. The checks also admit zero target
rings and trivial vector carriers without extra hypotheses.

The composition, functor, and preservation lemmas are intrinsic laws of
these definitions. They are not proofs of the later source assertions
about tensor or Hom constructions. The actual commuting-bimodule
framework, tensor-based forgetful functor, Hom-based pseudo-forgetful
functor, their comparison with scalar restriction, agreement of the two
nondegenerate parts, induction, adjunction, and exactness remain separate
successors. In particular this module does not claim that arbitrary
nonunital scalar homomorphisms preserve nondegeneracy or complete
Renard I.2.3.
