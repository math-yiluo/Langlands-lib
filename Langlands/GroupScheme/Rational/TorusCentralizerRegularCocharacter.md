# Regular descended cocharacters of torus centralizers

This module is an internal prerequisite for the quasi-split Steinberg quotient
task. Suppose the whole centralizer of a split torus is represented by an actual
torus, as for a maximal split torus of a quasi-split group. The module then
produces a cocharacter of that centralizer torus that is defined over the
original field, is regular after base change to any splitting field and is fixed
by the ordinary Galois action. A ground-field cocharacter that is regular after
base change is the input needed to choose a Galois-stable positive system of
roots. The module does not prove that such a torus centralizer exists, and it
uses no root datum and no reductivity hypothesis.

## Generic regularity criterion

`isRegularCocharacter_of_centralizer_isRepresentedBy_torus` works over an
arbitrary field `k` in universe `u`. Let `G/k` be affine and locally of finite
type, and let `i : T → G` come from a split commutative torus `T/k`. Let
`ν : X_*(T)` be a cocharacter. Suppose the dynamic centralizer of the composite
`ν ≫ i` is represented by `i` itself, in the Library's sense `IsRepresentedBy`
(a monomorphism whose range is that subgroup functor on every test scheme). Then
`ν` is regular in the sense of `IsRegularCocharacter i ν`: every actual root
`α ∈ roots i` (a nonzero character with a nonzero Lie weight space) satisfies
`⟨α, ν⟩ ≠ 0`.

**Proof as implemented.** Suppose `⟨α, ν⟩ = 0` and take a nonzero Lie vector
`X` in the `α` weight space. `weightSpace_le_weightSpace_cocharacter` puts `X`
in the weight space of `ν ≫ i` for the character `t ↦ t^{⟨α, ν⟩} = t^0`. The
proved dynamic Lie theorem `dynamicLie` then puts the dual-number point of `X`
in the dynamic centralizer of `ν ≫ i`. By the representation hypothesis that
point lies in the range of `i`, hence in the torus centralizer of `i`
(`range_le_torusCentralizer`). By
`Lie.mem_weightSpace_zero_of_mem_torusCentralizer`, `X` therefore lies in the
zero `T`-weight space. Since `α ≠ 0` and `T` is split, `weightSpace_disjoint`
makes the `α` and `0` weight spaces disjoint, so `X = 0`. This contradicts the
choice of `X`.

## Actual torus centralizers

Fix a commutative group `A/k`, a homomorphism `a : A → G` and a value
`C : TorusCentralizerTorusData a`. Such a value consists of an actual torus
`C.torus`, a closed-subgroup inclusion `C.inclusion` into `G`, and the fact that
this inclusion represents the whole centralizer of `a` on every test scheme.

- `selfCentralizing` proves that the centralizer of `C.inclusion` equals its
  range. One inclusion is `range_le_torusCentralizer`. For the other, an element
  centralizing the torus also centralizes `A`, because `a` factors through the
  torus by the canonical factor `torusCentralizerFactor a C.represents`. It
  therefore lies in the centralizer of `a`, which is the range.
- `isMaximalTorus` concludes from this, through the published
  `isMaximalTorus_of_torusCentralizer_eq`, that `C.inclusion` is a maximal torus
  of `G`. Neither reductivity of `G` nor maximality of `A` is used.
- `isMaximalTorus_baseChange` gives maximality of the base-changed inclusion
  `i_K : T_K → G_K` for every field extension `K/k`, through
  `isMaximalTorus_baseChange_of_torusCentralizer_eq`. No separate
  maximal-torus base-change premise is needed. This theorem omits the affine
  and finite-type assumptions on `G`.

The remaining declarations assume `G/k` affine and locally of finite type.

- `regularCocharacter hA`, for a split torus `A` (`hA`), is the published
  separating cocharacter `centralizingCocharacter hA a` of `A`, followed by the
  canonical factor of `A` into `C.torus`. It is a cocharacter of the
  ground-field torus `C.torus`.
- `regularCocharacter_centralizer` proves that the whole dynamic centralizer of
  this cocharacter composed with `C.inclusion` is the range of `C.inclusion`.
  The composite with the factor is the composite with `a`
  (`torusCentralizerFactor_comp`). `centralizingCocharacter_spec` identifies its
  dynamic centralizer with the centralizer of `a`, which `C` represents.

## Base change to a field extension

Let `K/k` be an arbitrary field extension with base map `b`. Write `T_K`, `G_K`
and `i_K` for the canonical base changes of the torus, the group and the
inclusion, and `ν_K` for the canonical lattice base change
`cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA)`.

- `regularCocharacter_baseChange_centralizer` proves that the dynamic
  centralizer of `ν_K ≫ i_K` is the range of `i_K`. The proof rewrites the
  lattice base change as the dynamic base change of the cocharacter
  (`cocharacterLattice.groupHom_baseChange_dynamic`), moves base change through
  the composite (`Dynamic.baseChangeCocharacter_comp`), and commutes dynamic
  centralizers with base change (`Dynamic.centralizer_baseChange`). It then
  applies the ground-field equality and `SubgroupFunctor.range_baseChangeHom`.
- `regularCocharacter_baseChange_isRegular` assumes in addition that `T_K` is
  split, as over any splitting field of `C.torus`. It proves
  `IsRegularCocharacter i_K ν_K`. Base change preserves the monomorphism part of
  `C.represents`, and with the previous equality this shows that `i_K`
  represents the dynamic centralizer of `ν_K ≫ i_K`. The generic criterion
  above then applies.
- `regularCocharacter_baseChange_galois` proves that the ordinary cocharacter
  Galois action `cocharacterLattice.galoisRepresentation k K C.torus σ` fixes
  `ν_K` for every `σ : K ≃ₐ[k] K`. The cocharacter is the base change of a
  ground-field cocharacter, so the published
  `cocharacterLattice.galoisRepresentation_baseChange` applies. No descent
  argument for invariant lattice elements is used, and `K/k` need not be
  finite, separable or Galois.

## Scope

The fields are arbitrary, with no finiteness, perfectness or infinitude
assumptions. The constructions depend only on the supplied torus centralizer
data and on the published separating cocharacter of a split torus. The module
does not prove that a maximal split torus of a quasi-split group has a torus
centralizer, and it does not construct a realized root datum, a pinning, a
Steinberg cross-section or the quotient. Those remain separate obligations of
the host task and its prerequisite tasks.
