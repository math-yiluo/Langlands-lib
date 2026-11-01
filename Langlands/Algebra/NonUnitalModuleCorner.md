# The fixed-part splitting and corner functor

## Source and scope

This unit implements the idempotent decomposition and unital corner action in
David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**, Chapter I conventions, printed page 6 / PDF page 12,
and the construction of the functor \(j_e\) in I.3.1, printed page 19 /
PDF page 25, including the decomposition (I.3.1.1). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The cited original pages were read. The 2020 edition is not used.

The first two pages of the registered supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were also read. Its corrections to the I.3.2 tensor injection and simple-module
arguments concern later constructions, which this unit does not implement.
No correction to the two constructions treated here was found on those pages.

All declarations below are in `Langlands.Algebra.NonUnitalModuleCorner`.
The ambient ring is an arbitrary associative `NonUnitalRing A`, possibly
noncommutative. The carrier `M` is an additive commutative group with the
specified original `NonUnitalModule A M` action. In particular, even if `A`
happens to have a unit, no identity-action law is assumed for `M`. The ring
universe `uA` and carrier universes `uM`, `uN`, `uP` are independent.
There are no local-unit, nondegeneracy, nontriviality, dimension, or scalar-field
hypotheses on the ambient construction.

The decomposition and corner action have exactly this generality in the
Chapter I conventions. Extending the functor to all original ambient modules
is an internal generalization of I.3.1, whose source assumes a complex
idempotented algebra and nondegenerate modules. Specializing the ring to that
algebra and restricting the functor along the published nondegenerate inclusion
gives the source's construction on underlying original modules and their
morphisms. The output has an ordinary unital corner-module structure.
This unit neither constructs an additional complex scalar action nor asserts
a categorical equivalence with a separately bundled complex module category.

The exactness proposition of I.3.1 is outside this definition unit. It requires
a separate proposition declaration and proof. I.3.2 induction, simple-class
correspondence, generated subcategories, and annihilator quotients are also
outside its scope.

## The fixed subgroup and split maps

The unit imports the original actions and actual intertwiners from
`Langlands.Algebra.NonUnitalModule`, the published pointwise Hom group
structures through `Langlands.Algebra.NondegenerateModuleAdditive`, and the
published coordinate and complementary kernel from
`Langlands.Algebra.NonUnitalModuleUniformity`. The actual corner ring comes
from `Langlands.Algebra.IdempotentedRing`.

`originalAction` is an abbreviation for `NonUnitalModule.toEndHom hM`, where
`hM` is the specified original action. Thus it is an actual nonunital ring
homomorphism from `A` to the additive endomorphisms of `M`.
`originalAction_apply` exposes that action's scalar operation;
`originalAction_mul` and `originalAction_zero` expose its multiplication and
zero laws. `originalAction_coordinate` identifies its value on an idempotent
with the existing `Idempotent.leftActionCoordinate`.

For an actual `e : Idempotent A`, `fixedPart e M : AddSubgroup M` has carrier

```text
{m : M | e.leftActionCoordinate m = m}.
```

Closure under zero, addition, and negation follows from the coordinate's
additivity. `FixedPart e M` is a dedicated name for its subtype, and
`fixedPartAddCommGroup e M` is exactly the inherited subgroup structure.
`coordinate_idempotent` follows from multiplicativity of the original action
and \(e^2=e\). Consequently `mem_fixedPart_iff_image` identifies fixed vectors
with the image of the original action of `e`, and `fixedPart_eq_range` is the
equality of actual additive subgroups.

The full additive maps and their formulas are:

| Declaration | Formula or identity |
| --- | --- |
| `inclusion e` | The subgroup inclusion \(x\mapsto x.val\) |
| `projection e` | \(m\mapsto\langle e\cdot m,\ e\cdot(e\cdot m)=e\cdot m\rangle\) |
| `coe_inclusion`, `coe_projection` | Equalities of the entire underlying functions with these formulas |
| `projection_inclusion` | `projection.comp inclusion = AddMonoidHom.id _` |
| `inclusion_projection` | `inclusion.comp projection = e.leftActionCoordinate` |
| `inclusion_zero`, `projection_zero` | Their values at zero |

The applied formulas `inclusion_apply` and `projection_apply` expose the same
underlying elements. These are additive maps. For a noncentral idempotent the
fixed subgroup need not be stable under all of `A`, so no ambient `A`-linearity
of the subgroup, inclusion, or projection is asserted.

## The actual unital corner action

`fixedPartModule e M` constructs an actual
`Module (Idempotent.Corner e) (FixedPart e M)`, using the published
`Idempotent.Corner.ring e` and `fixedPartAddCommGroup e M`. Its scalar operation is

```text
a • x = ⟨originalAction (Idempotent.Corner.toAmbient e a) x.val, ...⟩.
```

`corner_action_mem` proves membership by associativity of the original action
and the corner support equation \(ea=a\). Multiplicativity and both
distributivity laws descend from `originalAction`; its additive endomorphisms
also give the vector-zero law, and its zero value gives the scalar-zero law.
The unit of the named corner ring has ambient value `e`, so its identity-action
law is precisely the defining property of a fixed vector. No ambient unit is
used.

`fixedPart_smul_val` gives the formula on ambient values.
`fixedPartModule_smul` gives the complete subtype formula using
`(fixedPartModule e M).toSMul.smul` explicitly. `fixedPart_smul` installs the
named corner ring, inherited group, and module locally in its statement;
`fixedPart_one_smul` states the unit law with those same structures.
These constructors do not accept an independently inferred action on the
fixed carrier or an independently supplied ring on the corner. A caller
working with competing instances can use these names and explicit original
structure parameters to select the construction.

## The additive decomposition

`residual e : M →+ M` is the actual additive map
`AddMonoidHom.id M - e.leftActionCoordinate`. Its complete function formula is
`coe_residual`, with applied and zero formulas `residual_apply` and
`residual_zero`.

The complementary subgroup is exactly the existing
`e.leftActionKernel (M := M)`, the kernel of the original additive coordinate.
`mem_kernel_iff_residual` reuses the published residual characterization, with
the image equation oriented as `residual e n = m`.
`kernel_eq_residual_range` identifies the kernel with the actual range of this
residual map. This is the source's \((1-e)M\). As Renard explicitly warns on
printed page 6, the symbol \(1\) here is an identity operator on the additive
group, not an assumed identity element of `A`.

`splitting e` is the actual additive equivalence

```text
M ≃+ FixedPart e M × e.leftActionKernel (M := M)
m ↦ (projection e m, ⟨m - e.leftActionCoordinate m, ...⟩)
(x,y) ↦ x.val + y.val.
```

`coe_splitting` and `coe_splitting_symm` are equalities of the complete forward
and inverse functions. `splitting_fst_val`, `splitting_snd_val`, and
`splitting_symm_apply` expose their applied formulas; `splitting_zero` retains
the value at zero. The forward map is additive because its two coordinates
are additive. The left inverse is the identity
\(e m+(m-e m)=m\). For the right inverse, a fixed vector satisfies \(ex=x\)
and a kernel vector satisfies \(ey=0\), so the two coordinates of \(x+y\)
are \(x\) and \(y\). This proves an additive-group decomposition, with no
claim of ambient `A`-linearity.

## Restrictions, naturality, and the functors

For every original `f : NonUnitalModuleHom A M N`, `map_mem_fixedPart` uses
`f.map_smul` to prove that `f` preserves fixed vectors.
`restrict e f` is the resulting actual corner-linear map, with formula
\(x\mapsto\langle f(x.val),\ldots\rangle\).
Its scalar law is the original intertwining equation at the ambient value
of a corner element.

`restrict_apply` exposes the value, while `coe_restrict` identifies the entire
function. `restrict_apply_zero`, `restrict_id`, `restrict_comp`,
`restrict_zero`, `restrict_add`, and `restrict_neg` give its zero-value,
identity, composition, zero-map, addition, and negation laws.
`restrictAddHom e` bundles restriction as an additive homomorphism on the
published pointwise Hom groups; `coe_restrictAddHom` identifies its underlying
function with `restrict e`.

The equalities `inclusion_naturality` and `projection_naturality` are
equalities of entire additive maps:

```text
inclusion_N ∘ restrict(f) = f ∘ inclusion_M
restrict(f) ∘ projection_M = projection_N ∘ f.
```

The first is definitional, and the second is `f.map_smul` at `e`.
These unbundled maps retain independent source, target, and composition-carrier
universes `uM`, `uN`, and `uP`.

`functor e` is the actual functor

```text
NonUnitalModuleCat.{uA,uM} A ⥤ ModuleCat.{uM} (Idempotent.Corner e).
```

It sends `M` to `ModuleCat.of _ (FixedPart e M)` and `f` to the morphism
whose linear map is `restrict e f`. `functor_obj` and `functor_map_hom` state
these formulas. Identity and composition are proved in the functor's fields
by equality of evaluations. `functor_additive` proves preservation of the
inherited pointwise Hom addition, and `functor_map_zero` and `functor_map_add`
expose the resulting laws.

`nondegenerateFunctor e` is definitionally
`nondegenerateInclusion A ⋙ functor e`, using the published inclusion.
It is the underlying original-module construction of Renard's \(j_e\).
Its `_obj` and `_map_hom` lemmas state its formulas.
`nondegenerateFunctor_additive` follows from additivity of the two factors;
its `_map_zero` and `_map_add` lemmas expose the corresponding laws.
As usual for these bundled categories, each functor fixes one carrier universe;
this restriction does not constrain the universe-general unbundled maps.

## Zero cases

No declaration requires a nonzero idempotent or a nonzero module.
`fixedPart_zero_idempotent` identifies the fixed subgroup for `e = 0` with
bottom. `projection_zero_idempotent` identifies the entire projection with
zero, `residual_zero_idempotent` identifies the residual map with the identity,
and `kernel_zero_idempotent` identifies the complementary kernel with top.
The general splitting formulas therefore give a zero first coordinate and
the original vector as second coordinate in this case.

`fixedPart_zero_action` explicitly installs the published zero original action
and proves that every fixed subgroup is bottom, even if the ambient ring is
unital and the chosen idempotent is its identity. Thus the construction does
not silently assume a unit law on the original action. Zero carriers are
allowed by all the constructors. These boundary identities and the bundled
maps, naturality formulas, and additive-functor structures are intrinsic
formalization infrastructure derived from the cited constructions.
