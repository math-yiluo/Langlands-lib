# Affine integral Tate comparisons for the multiplicative group

This is an internal specialization of the published actual Gm torsion-to-roots
comparison. It composes `integralEquiv` from `MultiplicativeDivisibility` with
the root map of the canonical ring isomorphism
`Scheme.ΓSpecIso R : Γ(Spec R, ⊤) ≅ R`. The root transport and its residue
linearity are the published `fullLinearEquiv` and `awayLinearEquiv` from
`TwistRational`. The prime-adic comparison used below is already constructed in
`MultiplicativePrimeAffine`. No new assertion from the original literature is
used; the provenance is composition of these existing constructions.

## Inputs and carriers

Let `S` be a scheme, `R` a commutative ring object, and `f : Spec R ⟶ S`
an arbitrary morphism. Let `P : ℕ → Prop` be any selection predicate.
The source of `affineIntegralEquiv f P` is the existing inverse limit of
the actual Gm torsion sections over `Spec R`, at positive orders satisfying
`P`. The target is the existing inverse limit of the groups of actual roots
of unity in `R` at the same orders. Both use the quotient-power transition
maps. The equivalence is linear over `Global.ProfiniteIntegerRing`, with
the previously constructed residue actions on both sides.

There are no characteristic, reducedness, finiteness, rank, connectedness,
nonemptiness or closure hypotheses on the ring or the selection.

## The selected affine equivalence

`affineIntegralEquiv` first applies `integralEquiv (Over.mk f) P`, then
maps each root in the global sections of `Spec R` through `ΓSpecIso R`.
Its inverse uses the inverse section isomorphism followed by the inverse
Gm comparison. The two `apply` formulas state these composites.
`evaluation_affineIntegralEquiv` identifies the coordinate of order `n`
as the finite-level Gm-to-roots equivalence followed by the root map of
the section isomorphism.

`continuous_affineIntegralEquiv` and its inverse theorem use continuity
of the two factors. The finite-level groups carry their existing discrete
topologies, and the limits have the product-subspace topologies.
`affineIntegralContinuousLinearEquiv` bundles the resulting continuous
linear equivalence; its application agrees with `affineIntegralEquiv`.
This does not require or assert that the finite-level groups are finite.

## Full and away comparisons

`affineFullContinuousLinearEquiv` takes `P` to be the constantly true
predicate, thus retaining every positive torsion order.

For any natural number `m`, `affineAwayEquiv f m` composes `awayEquiv`
with `awayLinearEquiv`. It is linear over
`Global.PrimeToProfiniteIntegerRing m` and retains exactly the orders
coprime to `m`. Its underlying function and inverse equal the selected
affine maps with `P(n) := Nat.Coprime n m`.
`affineAwayContinuousLinearEquiv` adds the already proved continuity
in both directions. No primality or nonzero hypothesis on `m` is needed.

The two `restrictAway` theorems assert the commuting squares for the
full-to-away coordinate restriction, in both the forward and inverse
directions. All maps in these squares keep or transport the same
coordinates, so their proofs are definitional equalities.

## Prime-power coordinates

For a prime `p`, and a proof that every `p^n` satisfies `P`,
`affinePrimeIntegralContinuousLinearEquiv_toPrime` states that extracting
the prime-power coordinates before the published affine prime-adic Gm
comparison agrees with extracting them after the selected affine comparison.
The `fullToPrime` theorem specializes this to the full limit.
The `awayToPrime` theorem specializes to the away limit when
`Nat.Coprime p m`. These identities are also definitional, since the
finite-level comparisons and canonical section maps are the same.

This unit constructs integral affine comparisons and their compatibility
laws only. It asserts no rational or adelic affine comparison, rational
topology, geometric monodromy or test-scheme base-change law, torsion
finiteness or rank, chosen trivialization of the twist, Weil pairing, or
completion of the parent PEL task.
