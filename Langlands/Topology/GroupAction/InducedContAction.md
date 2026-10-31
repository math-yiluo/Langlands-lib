# Induction and restriction of actual continuous topological actions

Worker 56 constructs the induction functor and its adjunction to restriction
on actual continuous topological actions. The namespace is
`Langlands.TopologicalInduction`. The module imports the published balanced
quotient from `InducedSpace` and reuses it by Lean name.

## Categories and restriction

Let `G : Type u` be a topological group and `H : Subgroup G` an arbitrary
subgroup with its subspace topology. The common space category is
`TopCat.{max u v}`. Thus its objects can include both the original space
and the actual product `G × X` and quotient used in induction. Both the
subgroup-action and full-group-action categories use this common universe.

Mathlib's `ContAction TopCat K` retains a topological space, a monoid
homomorphism from `K` to its continuous endomorphisms, and joint continuity
of the resulting action. The published identity self-forgetful functor
`topCatSelfForget` is selected locally. The private action and continuity
instances recover the action already present in each object; they do not
replace its action or topology.

`restrictAction H` is Mathlib's restriction functor along the continuous
subgroup homomorphism `H.subtype`. It retains the underlying space, its
topology and all continuous equivariant maps. Its subgroup action is
`h • y = (h : G) • y`.

## Induction functor

For a continuous `H`-action `X`, `inducedAction H X` has underlying space
the published `Space H X.obj.V`, namely the balanced quotient `G ×_H X`
with its product-quotient topology. Its `G`-action is left multiplication:

`a • [g,x] = [a*g,x]`.

The action laws and joint continuity are inherited from the constructed
quotient action. Each fixed action map is continuous, so the action
bundles as an actual object of `ContAction TopCat G`.

For a continuous `H`-equivariant map `f : X ⟶ Y`, `inducedMap H f`
extends `x ↦ unit H (f x)` across the quotient. The original unit's
subgroup equivariance and equivariance of `f` prove that extension is
well defined. Continuity of the unit and `f` proves continuity of the
extension; the published lift law proves full-group equivariance.
`inducedMap_mk` gives its value:

`[g,x] ↦ [g,f(x)]`.

`induction H` bundles these objects and maps as a functor. Quotient
induction reduces its identity and composition laws to this formula and
the corresponding identity and composition of the original maps.

## Hom equivalence and naturality

For `X : ContAction TopCat H` and `Y : ContAction TopCat G`,
`restrictHom H` sends a continuous equivariant morphism `F : Ind(X) ⟶ Y`
to the morphism

`x ↦ F([1,x])`.

Composition with the continuous unit proves continuity. The unit's
subgroup-equivariance law and the equivariance of `F` prove that this
is a morphism to `restrictAction H Y`. `restrictHom_apply` states the
formula.

Conversely, `extendHom H` sends `f : X ⟶ restrictAction H Y` to the
published quotient lift of its unchanged underlying continuous map.
Its value, recorded in `extendHom_mk`, is

`[g,x] ↦ g • f(x)`.

Here the action on the right is the original `G`-action on `Y`.
The original lift construction proves continuity and full-group
equivariance. No extension map or inverse equivalence is assumed.

`inductionHomEquiv H X Y` packages these maps as an equivalence

`(Ind(X) ⟶ Y) ≃ (X ⟶ Res(Y))`.

For extension after restriction, quotient induction writes every point
as `[g,x] = g • [1,x]`, and equivariance of `F` proves that the resulting
map equals `F`. For restriction after extension, the published lift-unit
formula gives `f(x)`. Extensionality of the continuous maps and equivariant
morphisms proves equality of the complete categorical morphisms.

`inductionHomEquiv_naturality_left_symm` proves that extension of `f ≫ k`
equals `Ind(f)` followed by extension of `k`. Quotient induction and the
two representative formulas prove this equality. The theorem
`inductionHomEquiv_naturality_right` proves that restriction of `F ≫ k`
equals restriction of `F` followed by `Res(k)`; evaluation at the unit
makes the two underlying maps definitionally equal.

## Adjunction, unit and counit

`inductionAdjunction H : induction H ⊣ restrictAction H` uses
`Adjunction.mkOfHomEquiv` with the constructed Hom equivalences and
the two proved naturality laws. Mathlib's construction supplies the
natural unit and counit and their triangle identities.
`inductionAdjunction_homEquiv` identifies its Hom equivalence with the
one constructed above.

`inductionAdjunction_unit_apply` identifies the unit at `X` with
`x ↦ [1,x]`. `inductionAdjunction_counit_mk` identifies the counit at
`Y` with `[g,y] ↦ g • y`, using the original `G`-action on `Y`.
Both formulas follow directly from the constructed Hom equivalence
and Mathlib's unit/counit definitions.

## Provenance and scope

The motivation is V. G. Berkovich, *Etale equivariant sheaves on p-adic
analytic spaces*, retained unfinished 1995–1996 Equish manuscript,
Construction 1.1.2, printed/PDF page 2. The original page was read
directly. Registered literature ID:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
registered folder SHA256:
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The retained member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Berkovich constructs an induced analytic space for an open subgroup by
coset copies, with the equivariant universal property. The present
categorical adjunction is an internally derived topological counterpart
of that universal property, using the actual balanced quotient and its
proved continuous extension from the published `InducedSpace`.
It works for arbitrary subgroups. No openness, finite index, separation
or nonemptiness assumption is imposed.

The implemented continuity is joint continuity of the underlying
topological action. Comparison with Berkovich's topology on analytic
automorphisms, an analytic atlas, analytic morphisms, equivariant etale
or quasi-etale sites, and Harris tower specializations remain separate
construction obligations.
