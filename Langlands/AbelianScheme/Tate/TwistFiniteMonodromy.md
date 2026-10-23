# Geometric monodromy on the actual finite roots of unity

Author: Worker 92.

This module constructs geometric monodromy on the existing
`TateTwist.Level Ω n = Additive (rootsOfUnity n Ω)`. The action is evaluation
of an automorphism of the actual finite geometric-fibre functor at the
multiplication kernel of the actual multiplicative group scheme. No root,
generator, basis, or trivialization is chosen.

## Internal provenance and hypotheses

This is an internal consequence of the published constructions in
`GroupScheme.Multiplicative`, `Tate.FiniteMonodromy`, and
`Tate.MultiplicativePrime`. Those modules supply the actual kernel and its
points-to-roots equivalence, evaluation on finite étale kernels, and the
torsion-to-roots comparison with its transition law. The present proofs
transport those constructions through their canonical equivalences. This
module makes no additional claim from original literature.

Fix a scheme `S`, a field `Ω`, a point `s : Spec (.of Ω) ⟶ S`, and

```lean
hfin : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
```

The acting group is the existing `FundamentalGroup s hfin`, with its existing
evaluation topology. At each order `n` the construction explicitly requires

```lean
[IsFinite (GroupScheme.mu S n).X.hom]
[Etale (GroupScheme.mu S n).X.hom]
```

These are assumptions about the actual structural morphism, not arbitrary
group or action data. Private local instances transfer them to the
definitionally identical multiplication kernel. This module does not prove
these geometric properties or install unconditional instances. In the usual
application, positivity of `n` and invertibility of `n` on `S` supply those
properties through a separate geometric theorem. The conditional evaluation
argument itself needs only the displayed assumptions, so it permits any
natural `n` for which they hold.

The intended geometric application takes an algebraically closed coefficient
field and a connected, locally noetherian base. No classification theorem or
identification with an absolute Galois group is asserted without those
hypotheses, or proved here with them.

## The affine level comparison

The declarations in `GroupScheme.Gm.TateComparison` allow any commutative ring
`R` and any morphism `s : Spec R ⟶ S`. `affineLevelEquiv s n` is

```text
Tate.Level (Gm S).toGrp (Over.mk s) n
  -- inverse of kernelLevelEquiv --> actual points of mu S n
  -- mu.levelEquiv --> TateTwist.Level R n.
```

`affineLevelEquiv_kernel` identifies its value on a kernel point.
`affineLevelEquiv_eq` proves that it is also the already published
`levelEquiv`, followed by the root map of the canonical isomorphism
`Γ(Spec R, ⊤) ≅ R`. Thus this affine presentation uses the existing root
carrier and canonical global-section identification.
`affineLevelEquiv_transition` proves compatibility with the actual
`[m/n]` torsion transition for `n ∣ m`. Its proof uses the published
global-section comparison and the ring-map naturality of root transitions.

## Action, scalars, and geometry

The remaining declarations are in `TateTwist.Geometry`. If `e` denotes
`affineLevelEquiv s n`, then `levelMonodromy s hfin n g` is

```text
x ↦ e (finiteLevelMonodromy (Gm S).toGrp s hfin n g (e.symm x)).
```

It is an additive automorphism of the actual root group.
`affineLevelEquiv_monodromy` states that `e` intertwines it with the
published finite-level action on `Gm`.
`levelMonodromy_kernel` states the geometric evaluation formula directly:
on a kernel point `y` the result is
`mu.levelEquiv n s (g.hom.app (ofOver (mu S n).X) y)`, in additive notation.
This ties the construction to the actual finite étale cover rather than a
supplied family of automorphisms.

`levelMonodromy_one` and `levelMonodromy_mul` follow by cancelling the
comparison and its inverse and using the existing action laws. The order is

```text
ρ(g*h)(x) = ρ(g)(ρ(h)(x)).
```

`levelMonodromyLinear` bundles this automorphism over the existing `ZMod n`
module structure. `ZMod.map_smul` proves its residue linearity from
additivity. `levelRepresentation` is the resulting group homomorphism into
the linear automorphism group, in the same composition order.
`levelAction` gives a locally installable `DistribMulAction`; no global
action instance is installed.

`continuous_levelMonodromy` proves joint continuity in `g` and `x` for the
existing group topology and discrete root-level topology. Both directions
of the comparison are continuous because their domains are discrete.
Composing them with the published joint continuity of
`finiteLevelMonodromy` proves the claim.
`levelAction_continuousSMul` packages it for exactly `levelAction`.

`level_finite` deduces finiteness of this root group from `hfin` applied to
the actual multiplication-kernel cover, through the existing finite-level
finiteness theorem and the comparison. It assumes neither a cardinality
formula nor a chosen generator.

Finally, `levelMonodromy_transition` assumes finite étaleness at both `n`
and `m` and proves, for `n ∣ m`,

```text
ρ_n(g)(transition Ω h x) = transition Ω h (ρ_m(g)(x)).
```

The proof writes `x` through the affine comparison, applies its transition
law, and invokes equivariance of the existing actual torsion transition.

## Scope

This focused unit constructs finite-level monodromy and its compatibility
with the actual `Gm` comparison. It does not yet construct the inverse-limit
or rational action, path transport, pointed base change, Weil pairings, or
PEL level structures. The geometric finiteness and finite étaleness
hypotheses remain explicit theorem dependencies.
