# The roots of the centralizer of a cocharacter: proof

Author: Worker 712.

This module proves the published proposition
`DynamicCentralizerRootsStatement`
([`Dynamic.CentralizerRootsStatement`](CentralizerRootsStatement.md)) as the
theorem

```text
Langlands.GroupScheme.dynamicCentralizerRoots : DynamicCentralizerRootsStatement.{u}
```

The theorem keeps every binder of the statement, at the same universe `u`. The
only axioms used are `propext`, `Classical.choice` and `Quot.sound`. The
module adds no other declarations.

## Setting

Fix a field `k`, a connected reductive `G`, a split torus `T` with
`i : T ⟶ G`, a cocharacter `ν` of `T`, a closed subgroup `z : Z ⟶ G`
representing `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)`, a proof
that `Z` is connected reductive, and `t : T ⟶ Z` with `t ≫ z = i`. Write
`dz = Lie.targetMapLinear z k : Lie(Z)(k) → Lie(G)(k)` for the differential
of `z`, and `g_n(ν)` for the weight space of the character `s ↦ s^n` of `𝔾_m`
acting through `ν ≫ i`. The goal is the equality of sets

```text
roots t = {α | α ∈ roots i ∧ latticePairing T α ν = 0}.
```

The proof only uses that `G` is smooth and affine (for the instances
`IsAffineHom` and `LocallyOfFiniteType` needed by `dynamicLie`), that `Z` is
affine, and the representability hypothesis. In particular `dz` is injective
because a representing morphism is a monomorphism (the first field of
`IsRepresentedBy`), via `Lie.targetMapLinear_injective`. The hypotheses
`IsSplitTorus T.toGrp`, `IsMaximalTorus i` and `IsClosedSubgroup z` are not
used.

## Published results used

- `dynamicLie` ([`Dynamic.LieProof`](LieProof.md)): a tangent vector `X` of `G`
  is a dual-number point of `Dynamic.centralizer χ` if and only if it lies in
  the weight-zero space of `𝔾_m` acting through `χ` (the first clause of
  `DynamicLieStatement`; Milne 13.33(c), CGP 2.1.8(1)).
- `SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear`
  ([`Rational.StandardLeviLieWeights`](../Rational/StandardLeviLieWeights.md)):
  for a representing morphism `z`, a tangent vector of `G` lies in the range of
  `dz` if and only if its dual-number point belongs to the subgroup functor.
- `lieKernelHomLinear_mem_weightSpace` and
  `lieKernelHomLinear_mem_weightSpace_iff`
  ([`Lie.Functoriality`](../Lie/Functoriality.md)): `dz` maps the weight space
  of `α` for `t` into the weight space of `α` for `t ≫ z`, and, `z` being a
  monomorphism, a vector of `Lie(Z)` lies in the weight space of `α` for `t`
  exactly when its image does for `t ≫ z`.
- `weightSpace_le_weightSpace_cocharacter`
  ([`Absolute.RegularCocharacterWeights`](../Absolute/RegularCocharacterWeights.md)):
  a weight vector of `α` for `i` lies in `g_n(ν)` with `n = ⟨α, ν⟩`.
- `weightSpace_disjoint` (same module) applied to the split torus `𝔾_m`
  (`isSplitTorus_gm`), together with `Gm.powerHom_injective`: `g_n(ν)` and
  `g_m(ν)` are disjoint when `n ≠ m`.

## The inclusion `⊆`

Let `α` be a root of `t`: `α ≠ 0` and the weight space of `α` for `t` contains
a vector `Y ≠ 0`. Its image `X = dz Y` lies in the weight space of `α` for
`t ≫ z = i`, and `X ≠ 0` since `dz` is injective. So the weight space of `α`
for `i` is nonzero and `α ∈ roots i`.

Since `X` is in the range of `dz`, its dual-number point lies in the
centralizer of `ν ≫ i`, so `X ∈ g_0(ν)` by `dynamicLie`. Also
`X ∈ g_n(ν)` with `n = ⟨α, ν⟩`. If `n ≠ 0`, the two spaces are disjoint and
`X = 0`, a contradiction. Hence `latticePairing T α ν = 0`.

## The inclusion `⊇`

Let `α ∈ roots i` with `⟨α, ν⟩ = 0`, and let `X ≠ 0` be in the weight space of
`α` for `i`. Then `X ∈ g_0(ν)`, so by `dynamicLie` its dual-number point lies
in the centralizer, and by representability `X = dz Y` for some `Y` in
`Lie(Z)(k)`. As `dz Y = X` lies in the weight space of `α` for `t ≫ z = i`,
the vector `Y` lies in the weight space of `α` for `t`. If that weight space
were zero, then `Y = 0` and `X = dz 0 = 0`, a contradiction. Since `α ≠ 0`,
`α` is a root of `t`.

## Relation to the literature

This is the argument indicated in the Markdown of the statement: by Milne
13.33(c) (or CGP 2.1.8(1)) the Lie algebra of `Z_G(ν)` is `g_0(ν)`, whose
nonzero `T`-weights are the roots `α` with `⟨α, ν⟩ = 0`. The Lean proof uses
the Library's `dynamicLie` for the identification of tangent vectors of the
centralizer, and the representing morphism `z` to pass between tangent vectors
of the centralizer functor and of `Z`.
