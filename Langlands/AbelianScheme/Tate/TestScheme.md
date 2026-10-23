# Restriction of actual Tate modules in the test scheme

Fix a scheme `S`, a group object `G : Grp (Over S)` with commutative
multiplication, and test schemes `T`, `T'`, `T''` over `S`. This module
constructs contravariant restriction along any morphism `a : T' ⟶ T`.
The declarations are in `Langlands.GroupScheme.Tate`.

## Internal provenance

The input `torsionPointsRestrict` from `AbelianScheme.Torsion` restricts
actual torsion sections by precomposition. `Tate.Integral` already supplies
the actual torsion kernels, their quotient-power transition maps and their
coherent-family limits. `Tate.Scalars` supplies the full and away compatible
residue actions. This module lifts the existing restriction maps through
these limits; it introduces no alternative torsion carrier or arbitrary
transport datum. All claims are internal consequences of these published
constructions and Mathlib's group-object precomposition laws.

## Finite levels and limits

`levelRestrict G a n` is `torsionPointsRestrict G (n : ℤ) a` in additive
notation, for every natural `n`, including zero. Its underlying section is
`a ≫ x`, as recorded by `toSection_levelRestrict`. The theorem
`levelRestrict_kernelLevelEquiv` identifies this restriction with
precomposition of sections of the actual multiplication kernel, using the
published kernel universal-property equivalence.

`levelRestrict_transition` proves that restriction commutes with the
transition from order `m` to order `n` whenever `n ∣ m`. After forgetting
the torsion condition, the equality says that precomposition commutes with
raising a group-object section to the power `m / n`.

For any predicate `P : ℕ → Prop`, `testRestrict G P a` applies these maps
to each coordinate of `Integral G T P`. The indices are positive natural
numbers satisfying `P`; no closure, nonemptiness or cofinality is required.
The transition equality establishes coherence. `evaluation_testRestrict`
records the coordinate formula.

`testRestrict_id` gives identity restriction. For `b : T'' ⟶ T'`,
`testRestrict_comp` states the contravariant composition law

```text
testRestrict G P (b ≫ a) =
  (testRestrict G P b).comp (testRestrict G P a).
```

The proofs reduce coordinatewise to the identity and associativity laws
for composition in `Over S`.

## Topology, scalars and naturality

`continuous_testRestrict` uses the existing product-subspace topology on the
limit and the discrete topology on each torsion level. Each coordinate is a
continuous evaluation followed by a map between discrete spaces. No
finiteness or compactness hypothesis is used or asserted.

`fullTestRestrict G P a` bundles the same function as a continuous linear map
over `Global.ProfiniteIntegerRing`. `awayTestRestrict G m a` bundles it over
`Global.PrimeToProfiniteIntegerRing m` on the orders coprime to any natural
modulus `m`. Their scalar laws follow coordinatewise from `ZMod.map_smul`.
The accompanying apply lemmas identify both bundles with `testRestrict`.

`testRestrict_restrictAway` shows that changing test schemes commutes with
restricting the set of orders from all positive orders to those coprime to
`m`. `testRestrict_map` shows that precomposition in the test scheme commutes
with the map induced by any homomorphism `f : G ⟶ H` of commutative group
objects. The first equality is definitional; the second follows from
associativity of section composition.

## Scope

These are restrictions of sections over a fixed base `S`. They do not
construct change of base for `S`, path transport between geometric fibre
functors, or monodromy. They apply to actual abelian schemes through their
existing commutative group objects. Rationalization, rank, finiteness,
perfect pairings and PEL level structures are not claimed here.
