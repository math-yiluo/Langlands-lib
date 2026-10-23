# Geometric path transport on integral prime-adic root twists

This internal construction gives transport on the existing prime-power
roots-of-unity inverse limit. It imports `TwistIntegralTransport` and
`TwistPrimeMonodromy`. All new declarations are in
`Langlands.TateTwist.Geometry`.

## Inputs and carriers

Fix a scheme `S`, fields `Ω`, `Ω'`, and, for composition, `Ω''` in the
same universe, and points `s`, `t`, `r` with those respective fields.
At each used point there is an explicit hypothesis that every actual
finite étale cover has a finite fibre, such as
`hs : ∀ Y : Cover S, Finite (Fiber s Y)`.

The input path is an actual natural isomorphism
`γ : fiberFunctor s hs ≅ fiberFunctor t ht`. It is supplied, not
constructed from connectedness or a classification theorem.
Let `p : ℕ` satisfy `[Fact p.Prime]`. Named instance families
`hμfin` and `hμet` require the structural maps of the actual schemes
`mu S (p ^ n)` to be finite and étale for every natural `n`, including
`n = 0`, whose order is one.

The carriers are the existing `TateTwist.Integral Ω p` and
`TateTwist.Integral Ω' p`. Their coordinates are actual roots of unity
of orders `p ^ n`; the transition from `n + 1` to `n` is the existing
quotient-power transition, hence the `p`th-power map. Their
`ℤ_[p]`-module structures use the existing residue maps
`PadicInt.toZModPow n`, and their topologies are the existing
product-subspace topologies. No field map, compatible roots, basis or
twist trivialization is chosen.

## Linear lift and evaluation

`primeLevelTransportLinear p n γ` is the actual
`levelTransport (p ^ n) γ` as a `ℤ_[p]`-linear map. Its scalar law
uses `levelTransportLinear` over `ZMod (p ^ n)`, with scalar
`PadicInt.toZModPow n a`.

`primeTransportHom p γ` uses the existing linear `TateTwist.lift`.
At coordinate `n` it applies `primeLevelTransportLinear p n γ` after
the source evaluation. Transition compatibility follows from
`levelTransport_transition` and the input family's coherence.
`evaluation_primeTransportHom` records the defining formula

```text
evaluation Ω' p n (primeTransportHom p γ x)
  = levelTransport (p ^ n) γ (evaluation Ω p n x).
```

The map therefore comes from evaluation of the actual geometric path
on the roots-of-unity covers at all prime-power orders.

## Equivalence, path laws and topology

`primeTransportHom_refl` and `primeTransportHom_trans` reduce to the
finite identity and composition laws by coordinate evaluation.
The composition order is

```text
T_(γ ≪≫ δ)(x) = T_δ(T_γ(x)).
```

`primeTransport p γ` bundles the linear equivalence. Its inverse is
`primeTransportHom p γ.symm`; the two inverse equations use composition,
path cancellation and identity. `evaluation_primeTransport` states the
same coordinate formula for this equivalence.
`primeTransport_refl`, `primeTransport_trans` and
`primeTransport_symm` retain the identity, composition and inverse laws.

For a loop `g : FundamentalGroup s hs`, `primeTransport_aut` identifies
this linear equivalence with the existing `primeMonodromy s hs p g`.
The proof uses equality at every root coordinate and the finite
`levelTransport_aut` identity.

`continuous_primeTransport` proves continuity for a fixed path:
each coordinate is finite transport after continuous evaluation,
then continuity into the product and its coherent-family subtype
gives continuity into the limit. `primeTransportContinuousLinearEquiv`
bundles continuity in both directions, with the inverse result obtained
from `γ.symm`. No topology or joint continuity in the path parameter
is asserted.

## Endpoint monodromy and different paths

`primeTransport_monodromy` proves

```text
T_γ(ρ_s(g)(x)) = ρ_t(pathConjugation γ g)(T_γ(x)).
```

The proof reduces to `levelTransport_monodromy` in each coordinate.
Both endpoint actions are the existing geometric prime-adic root
monodromy, and the group map is the actual path conjugation.

For paths `γ, δ` from `s` to `t`, `primeTransport_change_path` proves

```text
T_δ(x) = ρ_t(γ.symm ≪≫ δ)(T_γ(x)).
```

It rewrites the target loop action as transport, uses composition and
cancels the reversed path. The formula records dependence by target
monodromy; it does not assert that arbitrary paths give equal transports.

## Compatibility with selected, full and away extraction

For `P : ℕ → Prop`, the selected comparison assumes finite étaleness
of the actual `mu` schemes at every positive index in `Index P`,
and `hP : ∀ n, P (p ^ n)`.
`toPrime_transport` states

```text
Divisibility.toPrime Ω' P p hP (integralTransport P γ x)
  = primeTransport p γ (Divisibility.toPrime Ω P p hP x).
```

The prime-power finite étale hypotheses on the right are exactly the
restrictions of the selected hypotheses along
`Divisibility.primePowerIndex P p hP`. Both sides apply the same
finite path map to the same source coordinates, so the proof is reflexivity.

`fullToPrime_transport` specializes to all positive orders, using
`fullTransport` and `Divisibility.fullToPrime`.
`awayToPrime_transport` specializes to orders coprime to a natural
modulus `m`, using `awayTransport` and `Divisibility.awayToPrime`,
and requires `h : Nat.Coprime p m`. The witness `h.pow_left n` retains
each prime power. Both proofs are reflexivity, with the same explicit
restriction of the corresponding finite étale hypotheses.

## Provenance and scope

The construction is internally derived from actual finite root path
evaluation, the existing prime-power linear inverse limit, the
selected integral transport and the published prime monodromy and
extraction maps. The proofs above explain the implemented route; no
new claim is attributed to external literature.

Finite étaleness, fibre finiteness and existence of a path remain explicit
inputs. Rational transport, base change, pairing compatibility and
canonical independence of PEL fixed-orbit sets remain separate work.
This unit asserts no rank result or comparison isomorphism for the
extraction maps.
