# Actual twist monodromy from invertible orders

Author: Worker 92.

This derived adapter composes the published theorem
`Langlands.GroupScheme.muFiniteEtale` with the existing actual roots-of-unity
monodromy constructions. Its declarations lie in
`Langlands.TateTwist.Geometry.InvertibleOrders`.

For an arbitrary scheme `S`, positive `n`, and
`IsUnit (n : Γ(S, ⊤))`, `finite` and `etale` supply the two morphism properties
of the actual group scheme `mu S n`. They are the two projections of the
published theorem; the underlying multiplication kernel is unchanged.

For `P : ℕ → Prop`, the existing index type `Index P` retains positivity
and `P n`. Given invertibility of every indexed order, `selectedFinite` and
`selectedEtale` provide the exact instance families used by the existing
selected twist actions. For a prime `p`, `primeFinite` and `primeEtale`
derive these inputs for every `p ^ n` from invertibility of `p`. This includes
`n = 0`, when the order is one. Positivity follows from primality; powers
preserve units, and natural-number casts preserve powers.

## Representations and continuity

All representations retain a field `Ω`, an actual point
`s : Spec Ω ⟶ S`, and
`hfin : ∀ Y : Cover S, Finite (Fiber s Y)`.
The fundamental group is the existing automorphism group of the actual
finite étale geometric-fibre functor with its existing topology.

The following abbreviations specialize published representations by supplying
the proved morphism-property inputs:

| Declaration | Carrier | Scalars |
| --- | --- | --- |
| `levelRepresentation` | `Level Ω n` | `ZMod n` |
| `integralRepresentation` | `Divisibility.Integral Ω P` | `Global.ProfiniteIntegerRing` |
| `rationalRepresentation` | `Divisibility.Rational Ω P` | `ℚ` |
| `primeRepresentation` | `Integral Ω p` | `ℤ_[p]` |
| `rationalPrimeRepresentation` | `Rational Ω p` | `ℚ_[p]` |

Each is a group homomorphism into linear equivalences, so the identity and
left-action composition laws are included in its type. The scalar actions,
coherent-root carriers, and geometric actions are precisely those already
constructed in `TwistFiniteMonodromy`, `TwistIntegralMonodromy`,
`TwistRationalMonodromy`, `TwistPrimeMonodromy`, and
`TwistRationalPrimeMonodromy`. No roots or bases are chosen.

`continuous_levelRepresentation`, `continuous_integralRepresentation`, and
`continuous_primeRepresentation` specialize the published joint-continuity
proofs, using the existing finite discrete and inverse-limit topologies.
This module makes no rational joint-continuity claim.

Taking `P := fun _ => True` gives the full selected integral and rational
twists, with invertibility required at every positive order.
Taking `P := fun n => Nat.Coprime n m` gives the prime-to-`m` versions,
requiring invertibility only at positive orders coprime to `m`.
These specializations retain the displayed scalar rings. The existing
away and finite-adelic scalar refinements can use `selectedFinite` and
`selectedEtale` directly with their own published scalar hypotheses.

## Pointed base change

`pullbackUnit b n` maps the unit along `b.appTop.hom`; preservation of
natural-number casts identifies it with the same order on the new base.
Thus no separate invertibility hypothesis on the new base is needed.

For `b : S' ⟶ S`, `t : Spec Ω ⟶ S'`, and the two existing fibre-finiteness
hypotheses `ht` and `hs`, each of the five
`...Representation_baseChange` theorems asserts equality of representations:
the representation at `t ≫ b`, restricted along the published pointed
fundamental-group map, equals the representation at `t`. The latter uses
the pulled-back unit witnesses.

The finite proof applies `levelMonodromy_baseChange` after extensionality
in the group element and root. The other four proofs apply the corresponding
published integral, rational, prime, or rational-prime theorem from
`TwistMonodromyBaseChange`, with the morphism properties supplied above.
The rational carriers and their scalar extensions are unchanged.

## Provenance and scope

This is an internal interface derived entirely from published Library
mathematics. The geometric input and its original-source provenance are
documented in [MuFiniteEtaleProof](../../GroupScheme/MuFiniteEtaleProof.md).
The action construction and topology are documented in
[TwistFiniteMonodromy](TwistFiniteMonodromy.md),
[TwistIntegralMonodromy](TwistIntegralMonodromy.md), and
[TwistPrimeMonodromy](TwistPrimeMonodromy.md).
The pointed comparison is documented in
[TwistFiniteBaseChange](TwistFiniteBaseChange.md) and
[TwistMonodromyBaseChange](TwistMonodromyBaseChange.md).
The adapter introduces no new geometric existence or comparison theorem.

Fibre finiteness remains explicit. This module does not infer it from a
Galois-category theorem, assert rank or freeness, or construct a twist
trivialization. It retains arbitrary same-universe bases and point fields;
algebraic closedness, connectedness and local noetherianness are not needed
for these formal consequences of the displayed hypotheses. This is a
roots-of-unity adapter, not a construction of the abelian Weil pairing or
of a canonical unpointed PEL functor.
