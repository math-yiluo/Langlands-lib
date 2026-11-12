# The canonical homogeneous orbit map in Renard III.3.2

This construction makes the change of quotient convention in Renard III.3.2
explicit on the original quotient spaces and actions. It also constructs
inverse image along the resulting continuous equivariant map. It does not
assert inverse continuity of the transitive set equivalence.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, III.3.2, printed p.84 / PDF p.90, the
transitive-action paragraph immediately before the induction functor.
Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
That paragraph invokes the II.3.3 Corollary for the homeomorphism with
`G/H`, then changes to `H\G` with the inverse right action to agree with
the induction convention. The maps below are an internal implementation
of that convention comparison and the associated inverse image.

## Original quotient and canonical map

The group `G : Type uG` is a topological group, and it acts jointly
continuously on the topological space `X : Type uX`. These universes are
independent in the orbit-map part. A chosen point `x : X` specifies the
actual subgroup `MulAction.stabilizer G x`.

`map x` is a continuous map from
`Langlands.Induction.LeftQuotient (MulAction.stabilizer G x)` to `X`.
It is literally the composition of the published
`Langlands.Induction.quotientInversion` with Mathlib's
`MulAction.ofQuotientStabilizer`. It therefore has the formula

```text
map x (H g) = g⁻¹ • x.
```

Continuity follows from the original quotient projection's universal
property and continuity of `g ↦ g⁻¹ • x`. `map_factor` records the exact
composition, and `map_origin` identifies its value at the original identity
coset with `x`.

The action on the source is precisely
`HomogeneousSections.homogeneousAction`, inherited from the published
inverse right translation: `g • (H k) = H (k g⁻¹)`.
`map_equivariant` checks that `map x (g • z) = g • map x z`.
No new quotient carrier, topology, stabilizer or group action is introduced.

## Set equivalence and separation

`map_injective` composes Mathlib's canonical orbit-map injectivity with
injectivity of the inversion homeomorphism. Under the additional actual
instance `MulAction.IsPretransitive G X`, `map_surjective` chooses `g`
with `g • x = y` and represents its preimage by `H g⁻¹`.
`transitiveEquiv` bundles exactly this bijection; its forward map is
`map x`, as recorded by `transitiveEquiv_apply`.

This is a set equivalence. The declarations do not assert that it is a
homeomorphism. In particular, they do not remove the sigma-compactness
hypothesis on `G` from Renard's transitive topological identification.
The published
`Langlands.Topology.RenardOrbitQuotient.TransitiveQuotientHomeomorphismStatement`
states the standard-quotient topological assertion separately.

When `X` is Hausdorff, `stabilizer_closed` proves that the actual stabilizer
is the closed equalizer of `g ↦ g • x` and the constant map at `x`.
Given the explicit source predicates
`Langlands.Topology.IsLocallyProfinite G` and
`Langlands.Topology.IsLocallyProfinite X`,
`quotient_isLocallyProfinite` applies the published closed-subgroup
left-quotient result in `HomogeneousSections`. It retains the Hausdorff
compact-open basis; it does not rely on transitivity or a homeomorphism
with `X`.

## Actual sheaf inverse image

This part specializes to `G X : Type`, matching the published actual
complex sheaf and inverse-image interfaces. Coefficients and section
carriers are universe zero as in `SectionActions.ActionSheaf`.

`pullback x` is the published `actionInverseImage` along `map x` with the
proved equivariance equation. It uses that construction's actual transport
Kan extension and sheafification, on all original action sheaves and maps.
It requires no transitivity, homeomorphism, local profiniteness or
sigma-compactness.

With the explicit locally profinite predicates on `G` and `X`,
`smoothPullback x` is the published `smoothActionInverseImage` along the
same map. Its target is Renard's category defined by smoothness on all
compact sections. `smoothPullbackToActionIso` records its original
underlying action-sheaf inverse image. This is a functor and a forgetful
comparison, with no assertion of an equivalence of sheaf categories.
The homogeneous induction functor, inverse-continuity theorem, and
homogeneous categorical equivalence remain separate obligations.
