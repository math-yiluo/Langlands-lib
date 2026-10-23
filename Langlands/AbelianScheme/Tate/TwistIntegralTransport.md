# Geometric path transport on integral roots-of-unity twists

This internal construction lifts `Geometry.levelTransport` to the existing
selected inverse limits of actual roots of unity. It imports
`TwistFiniteTransport` and `TwistIntegralMonodromy`; all new declarations
belong to `Langlands.TateTwist.Geometry`.

## Hypotheses and existing objects

Fix a scheme `S`, fields `Ω`, `Ω'`, and, for composition, `Ω''` in the
same universe, and points `s : Spec Ω ⟶ S`, `t : Spec Ω' ⟶ S`,
`r : Spec Ω'' ⟶ S`. Each used point has an explicit finite-fibre
hypothesis such as `hs : ∀ Y : Cover S, Finite (Fiber s Y)`.
The input path is an actual natural isomorphism
`γ : fiberFunctor s hs ≅ fiberFunctor t ht`.

For a predicate `P : ℕ → Prop`, `Index P` consists of the positive
integers satisfying `P`. Explicit instance families `hμfin` and `hμet`
require that the structural morphism of the actual scheme `mu S n.val`
is finite and étale at every `n : Index P`. The construction does not
prove these hypotheses from invertibility of the orders. There is no
assumption or conclusion about existence of a path. Algebraic closure
and connectedness are not required for this conditional construction.

The source and target are exactly `Divisibility.Integral Ω P` and
`Divisibility.Integral Ω' P`: coherent root families for the existing
quotient-power transitions, with their additive group structures and
product-subspace topologies. Transport requires no field map between
`Ω` and `Ω'`, compatible roots, basis, or twist trivialization.

## Coordinate construction and path laws

`integralTransportHom P γ` uses `Divisibility.lift` with coordinate maps

```text
x ↦ levelTransport n.val γ (Divisibility.evaluation Ω P n x).
```

Coherence follows by moving finite transport across the existing
transition using `levelTransport_transition`, then applying the
coherence of `x`. `evaluation_integralTransportHom` states the displayed
coordinate formula by reflexivity.

`integralTransportHom_refl` proves that the identity path acts
identically, coordinate by coordinate. `integralTransportHom_trans`
proves that `γ ≪≫ δ` first transports by `γ` and then by `δ`, by
reducing equality to all coordinates and using `levelTransport_trans`.

`integralTransport P γ` bundles an additive equivalence whose inverse
is `integralTransportHom P γ.symm`. Both inverse equations follow from
the composition and identity laws. `evaluation_integralTransport`
retains the same coordinate formula, and `integralTransport_refl`,
`integralTransport_trans`, and `integralTransport_symm` state the
identity, composition, and inverse laws for this equivalence.

For a loop `g : FundamentalGroup s hs`, `integralTransport_aut` identifies
the entire additive equivalence with `integralMonodromy s hs P g`.
The proof checks each root coordinate using `levelTransport_aut`.
The fundamental group and action are thus the existing geometric ones;
no independent action is supplied.

## Topology and scalars

`continuous_integralTransport` proves continuity for a fixed path.
Each coordinate is the composite of the continuous evaluation map
and the existing continuous finite transport. Continuity into the product
and then its coherent-family subtype gives the result.
No topology or joint continuity assertion on the space of paths is made.

`integralTransport_full_smul` proves

```text
T_γ(a • x) = a • T_γ(x)
```

for `a : Global.ProfiniteIntegerRing`. At the coordinate `n`, it is the
`ZMod n.val`-linearity of `levelTransportLinear n.val γ`, applied to
`GroupScheme.Tate.fullReduction P n a`. The scalar actions are precisely
the existing residue actions on both limits.
`integralTransportLinearEquiv` bundles this law.
`integralTransportContinuousLinearEquiv` adds continuity in both
directions, using the same continuity theorem for `γ.symm`.

## Geometric monodromy and choice of path

`integralTransport_monodromy` proves

```text
T_γ(ρ_s(g)(x)) = ρ_t(pathConjugation γ g)(T_γ(x)).
```

It reduces to `levelTransport_monodromy` at every coordinate.
The conjugation is the actual isomorphism of geometric fundamental
groups induced by the same path.

For two paths `γ, δ` from `s` to `t`,
`integralTransport_change_path` proves

```text
T_δ(x) = ρ_t(γ.symm ≪≫ δ)(T_γ(x)).
```

The loop is at the target point. The proof rewrites loop monodromy
as transport, applies composition and cancels the reverse path.
This describes the exact dependence on the path; it does not claim
that two path transports are equal.

## Full and away systems

`fullTransport` specializes to `P = True`, with explicit finite étale
hypotheses at every positive order.
`awayTransport m` specializes to `P n = Nat.Coprime n m`, with
finite étaleness required only at those retained orders. The modulus
`m` is any natural number. Identity, composition, inverse, evaluation,
loop and monodromy laws for these specializations follow directly from
the selected declarations.

`awayTransport_smul` proves linearity for the additional existing action
of `Global.PrimeToProfiniteIntegerRing m`, coordinatewise using
`GroupScheme.Tate.awayReduction m`. `awayTransportLinearEquiv` and
`awayTransportContinuousLinearEquiv` package this scalar law and
continuity in both directions.

`restrictAway_transport` states that the existing restriction
`Divisibility.restrictAway` commutes with transport along the same path.
It uses all-positive-order finite étale hypotheses for the full source,
and restricts those exact hypotheses for the away target. Both sides
have the same coordinate function, so its proof is reflexivity.

## Provenance and scope

This is an internal derivation from finite geometric root transport,
the existing coherent-family limit, its residue scalar actions and
integral geometric monodromy. Its proofs are described above; no new
claim is attributed to external literature. The approach parallels
the published abelian-scheme `IntegralTransport` construction, while
the carriers and finite maps here are the actual roots-of-unity twists.

Prime-power and rational transport, pointed base change, pairing
compatibility, existence of paths, and canonical independence of PEL
fixed-orbit sets remain separate work. This unit asserts no completion
of those obligations.
