# Coverings for actual rational-spectrum subgroup restriction

This internal construction specializes the generic induced subgroup covering to
an existing arrow of `OpenSubgroupTransport`. It identifies the original map
before transferring the product chart, covering and properness results.
The only imported construction modules are `InducedRationalSpectrum` and
`Langlands.Topology.GroupAction.InducedSubgroupCovering`; neither is modified.
No external mathematical theorem is claimed or assumed by this specialization.

## Input and original objects

The complete ultrametric normed field `K` and the presented strict affinoid
algebra `P` have universe `u`. The topological group `G` has an independent
universe `v`, and `ρ : RationalSpectralAction G P` is its original continuous
spectral action. Let `U` and `V` be open subgroups of `G`, `h : V ≤ U`, and
`d : ρ.InvariantRationalDomain U`. Set

- `Y := (inclusion U).obj d`;
- `X := (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)`;
- `D := U ⧸ V.toSubgroup.subgroupOf U.toSubgroup`.

Both local spectra are the original `BanachSpectrum d.obj.algebra`, in universe
`u`, with their original topologies. `X.InducedSpectrum` and
`Y.InducedSpectrum` are the existing balanced quotient spaces, in universe
`max u v`. The original arrow is `f := subgroupRestriction h d : X ⟶ Y`.
Its local bounded restriction, already constructed in `OpenSubgroupTransport`,
is `BoundedAlgHom.id K d.obj.algebra`. Its induced map and continuous full
`G`-action are those of `InducedRationalSpectrum`.

There are no finite-index, compactness, local compactness, separation,
nonemptiness or additional action-compatibility premises for the product chart,
covering, or fiber homeomorphism. The action and its continuity are supplied by
the original rational objects. Finite fibers and properness additionally use
`Finite D`.

## Identity on the local spectrum and exact original action

`subgroupRestriction_label` proves that `f.label = 1` by reduction.
`subgroupRestriction_localSpectrumMap` proves that the original local spectrum
map sends every `x : BanachSpectrum d.obj.algebra` to `x`. The proof rewrites the
original bounded restriction to the bounded identity and uses extensionality of
Banach-spectrum points. This concerns the original contravariant spectrum map,
not an arbitrarily chosen identity map.

`subgroupRestriction_localSpectrumAction` proves by `rfl` that the original
`V`-action on `X.LocalSpectrum` is exactly the original `U`-action on
`Y.LocalSpectrum` composed with `Subgroup.inclusion h`. The displayed subgroup
inclusion uses `V.toSubgroup ≤ U.toSubgroup`, the same predicate as `h`.
The statement explicitly selects `localSpectrumSubgroupMulAction Y`, so Lean
need not reconstruct the rational object from the action's carrier.

## Equality with the original induced map

`subgroupRestriction_inducedMap_eq` proves an equality of continuous maps:

```text
f.inducedMap = TopologicalInduction.subgroupMap h.
```

The right side uses precisely `Y.LocalSpectrum` with its original `U`-action
and its original continuity instance. Its source action is the restriction of
that action along `V → U`; by the preceding definitional equality this is the
action on the original `X.InducedSpectrum`. No homeomorphism or change of
source topology is inserted into the map equality.

The proof uses quotient induction on an original representative `[g,x]`.
The existing formula for `f.inducedMap` gives
`[g * f.label⁻¹, f.localSpectrumMap x]`. The label and local identity results
reduce this to `[g,x]` in the target quotient, exactly the representative
formula for the generic subgroup map. In particular, the existing full
`G`-equivariance of `f.inducedMap` is retained.

## Product chart and covering

`subgroupRestrictionProductHomeomorph h d` constructs

```text
X.InducedSpectrum ≃ₜ Y.InducedSpectrum × D.
```

It directly specializes `TopologicalInduction.subgroupProductHomeomorph` using
the original target action and the openness of both original subgroups.
The generic chart uses chosen coset representatives, and no equivariance of
this chart is asserted.

`subgroupRestrictionProductHomeomorph_fst` proves, for every original source
point `z`,

```text
(subgroupRestrictionProductHomeomorph h d z).1 = f.inducedMap z.
```

This follows from the generic projection equation and the proved equality
of the actual continuous maps. It ensures that all following results concern
the original rational subgroup-change map.

`subgroupRestriction_inducedMapEvenlyCovered h d y` constructs
`IsEvenlyCovered f.inducedMap y D` for every original target point `y`.
The generic theorem obtains the discrete relative coset space from openness,
then transports the product projection's covering through the product chart.
`isCoveringMap_subgroupRestriction_inducedMap` converts this to Mathlib's
`IsCoveringMap` predicate using the entire original fiber as each covering's
fiber space. Neither theorem requires finite relative index.

## Entire fibers, degree and properness

`subgroupRestrictionFiberHomeomorph h d y` is a homeomorphism

```text
D ≃ₜ f.inducedMap ⁻¹' {y}.
```

The codomain is the literal subtype of all original source points mapping to
`y`, with its original subtype topology. It is obtained from
`IsEvenlyCovered.fiberHomeomorph` and covers the entire fiber.

`finite_subgroupRestriction_inducedMap_fiber` transports `Finite D` through
that homeomorphism to prove finiteness of each entire original fiber.
`card_subgroupRestriction_inducedMap_fiber` proves

```text
Nat.card (f.inducedMap ⁻¹' {y}) = V.toSubgroup.relIndex U.toSubgroup.
```

The cardinality theorem has no finiteness premise: `Nat.card_congr` identifies
the cardinality with that of `D`, which is the definition of this relative
index in Mathlib. `Nat.card` is zero on an infinite type; the homeomorphism
still describes the full infinite fiber. For finite `D`, this is the usual
positive finite relative index and the degree is independent of `y`.

`isProperMap_subgroupRestriction_inducedMap` proves properness of the original
map under `Finite D`. It rewrites by the actual map equality and applies the
generic properness theorem. There, finite relative cosets form a compact
factor, and the product projection is proper without a compactness or
separation hypothesis on the original spectrum or target.

## Scope retained

This supplies genuine covering and finite-fiber facts for subgroup change
without changing the original rational presentation. General rational-domain
restriction maps need not be coverings and are not covered by this result.
The next use is to discharge covering and finite-fiber premises for the existing
ordinary-open coefficient traces and support pushforwards on these particular
arrows. The present module does not construct their arithmetic Hecke
identification, an analytic or etale chart, higher derived trace, a Shimura
specialization, or the Harris comparison; these remain obligations of the
broader task.
