# Actual induced topological spaces

This module constructs the underlying topological induction of a subgroup
space. The namespace is `Langlands.TopologicalInduction`. All new code and
prose are by Worker 36. The construction is independent of the analytic
geometry modules and is intended for their actual rational spectra.

## Inputs and balanced quotient

Let `G : Type u` be a group, `H : Subgroup G` an actual subgroup, and
`X : Type v` an actual `H`-set. The type `Representatives H X` is a wrapper
for `G × X`, with the action

`h • (g,x) = (g * h⁻¹, h • x)`.

The wrapper separates this action from the usual componentwise product
action. `Space H X` is its actual orbit quotient, and `mk H g x` is the
class `[g,x]`. Its equality criterion is proved in `mk_eq_mk_iff`:

`[g,x] = [k,y]` if and only if there exists `h : H` such that
`g = k * h⁻¹` and `x = h • y`.

In particular, `mk_subgroup_smul` and `mk_balance` prove the balancing
relations `[g*h⁻¹,h • x] = [g,x]` and `[g*h,x] = [g,h • x]`.
No induced carrier or quotient comparison is assumed as an input.

## Full group action and distinguished copy

Left multiplication on representatives respects the orbit relation. The
constructed `MulAction G (Space H X)` has evaluation

`a • [g,x] = [a*g,x]`.

Its identity and multiplication laws are proved on representatives. The map
`unit H : X → Space H X` is `x ↦ [1,x]`; `unit_injective` proves it is
injective using the equality criterion, and `unit_subgroup_smul` proves

`unit H (h • x) = (h : G) • unit H x`.

Every class `[g,x]` is `g • unit H x`, as recorded by `smul_unit`.
The actual subgroup and group labels are retained, including any kernel of
the action on `X`.

## Quotient topology and open embedding

Now suppose `G` is a topological group, `X` is a topological space, and its
`H`-action is jointly continuous. The subgroup uses its subspace topology.
The representative wrapper has the product topology and `Space H X` has
the orbit quotient topology. The subgroup translations of representatives
are continuous: the first coordinate is right multiplication by a fixed
inverse and the second coordinate is a fixed action on `X`.

Mathlib's open orbit-projection theorem gives `isOpenQuotientMap_mk`.
To descend joint continuity of the full `G`-action, the proof takes the
product of this open quotient map with the identity on `G`. The composite
upstairs is the continuous map `(a,(g,x)) ↦ [a*g,x]`. The resulting
`ContinuousSMul G (Space H X)` therefore proves joint continuity;
it does not only prove continuity for each fixed group element.
`continuous_unit` follows from the representative projection.

When `hH : IsOpen (H : Set G)`, the unit is an open embedding, proved in
`isOpenEmbedding_unit`. The proof uses the actual homeomorphism
`subgroupTwist` of `H × X`,

`(h,x) ↦ (h⁻¹,h • x)`.

This is an involution with continuous coordinates. Composing it with the
open inclusion `H × X → G × X` and the open orbit projection gives
`unit H ∘ Prod.snd`. Since the second projection is continuous and
surjective, openness descends to `unit H`. Its already proved continuity
and injectivity complete the open-embedding proof. This argument permits
empty `X` and does not require finite index or separation axioms.

## Continuous equivariant universal property

Let `Y : Type w` be a `G`-set, with its universe independent of `u` and `v`.
For a map `φ : X → Y` satisfying

`φ (h • x) = (h : G) • φ x`,

`lift φ hφ : Space H X → Y` is constructed by quotient descent of
`(g,x) ↦ g • φ x`. The balancing relation preserves this value by the
subgroup equivariance of `φ` and the action laws in `Y`.
`lift_mk`, `lift_unit`, and `lift_smul` prove its evaluation, extension,
and full-group equivariance. `lift_unique` proves that every equivariant
map with the same unit restriction equals this lift, by evaluation on
`g • unit H x`.

If `Y` is a topological `G`-space and `φ` is continuous, the map on
representatives is continuous and hence so is its quotient lift.
`extend` bundles this continuous extension. The selected definition
`equivariantMapEquiv` is an equivalence between the subtype of continuous
`G`-equivariant maps `Space H X → Y` and the subtype of continuous
`H`-equivariant maps `X → Y`. Its forward map is restriction along the
unit; its inverse is the constructed extension. Both inverse identities
are proved. The universal property itself works for an arbitrary
subgroup; openness is needed for the open-embedding conclusion above.

## Provenance and scope

The original motivation is V. G. Berkovich, *Etale equivariant sheaves on
p-adic analytic spaces*, retained unfinished 1995–1996 Equish manuscript,
Construction 1.1.2, printed/PDF page 2. Registered literature ID:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
registered folder SHA256:
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The retained member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The original page was read directly before implementation.

Berkovich constructs an induced analytic space by disjoint copies indexed
by left cosets of an open subgroup and gives its equivariant universal
property. This module supplies derived underlying topological
infrastructure via a balanced orbit quotient, proving the corresponding
continuous universal property and open unit embedding directly. It does
not construct the manuscript's analytic atlas, a coset-indexed comparison
homeomorphism, induction in stages, or its claimed retraction for a general
subgroup space. It also does not define analytic morphisms, etale sites,
site equivalences, or a cohomology comparison. Rational-spectrum
specialization and analytic structure remain separate construction
obligations.
