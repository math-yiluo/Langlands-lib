# Geometric monodromy on prime-adic roots-of-unity limits

This internal construction lifts the published finite geometric root action to
the existing prime-adic Tate twist. It imports `TwistIntegralMonodromy` and
`TwistPrimeComparison`; it does not choose compatible roots or a basis. All
declarations below are in `Langlands.TateTwist.Geometry`.

## Hypotheses and existing carriers

Fix a scheme `S`, a field `Ω`, and a point `s : Spec Ω ⟶ S`. The hypothesis
`hfin : ∀ Y : Cover S, Finite (Fiber s Y)` supplies finiteness of the actual
finite étale fibres used to define `FundamentalGroup s hfin`. This group is the
automorphism group of the existing finite-fibre functor, equipped with its
evaluation topology.

Fix a natural prime `p`, with `Fact p.Prime`. The primary constructions take
named instance families `hμfin` and `hμet`: the structural morphism of the actual
scheme `mu S (p ^ n)` is finite and étale for every natural `n`, including zero.
No finite étaleness at other orders is assumed. These hypotheses remain
explicit; this module does not derive them from invertibility of `p` on `S`.
Algebraic closure of `Ω` and connectedness or local noetherianity of `S` are
conditions of the intended geometric application, not needed by this
conditional construction.

The carrier is the published `TateTwist.Integral Ω p`: coherent sequences in
`Level Ω (p ^ n)`, where `Level` is the additive form of the actual group of
roots of unity in `Ω`. Successive transitions are the existing power maps.
The module structure is the existing `ℤ_[p]` action through
`PadicInt.toZModPow`, and the topology is the existing subspace topology of the
product of discrete levels.

## Construction and action laws

`primeLevelMonodromyLinear` regards finite geometric evaluation as a
`ℤ_[p]`-linear map. Its scalar law is the published finite residue linearity
applied to `PadicInt.toZModPow n a`.

`primeMonodromyHom` uses the existing universal linear lift `TateTwist.lift`.
For each `g : FundamentalGroup s hfin`, its `n`th coordinate is

```text
levelMonodromy s hfin (p ^ n) g (evaluation Ω p n x).
```

The finite transition-equivariance theorem and the coherence of `x` prove
coherence of this sequence. `evaluation_primeMonodromyHom` records that
coordinate formula. The finite action comes from evaluation on actual
`mu`-kernel points through the canonical affine comparison, as established in
`TwistFiniteMonodromy`; no arbitrary action is an input here.

`primeMonodromyHom_one` and `primeMonodromyHom_mul` prove the left-action laws
by coordinate extensionality. In particular, the product order is
`ρ(g * h)(x) = ρ(g)(ρ(h)(x))`. `primeMonodromy` is the resulting
`ℤ_[p]`-linear equivalence, with inverse given by the same construction at
`g⁻¹`. Its coordinate formula is `evaluation_primeMonodromy`.
`primeRepresentation` bundles these equivalences and action laws as a monoid
homomorphism.

## Continuity

`continuous_primeMonodromy` proves joint continuity in the group element and
the root sequence. Each output coordinate is the published continuous finite
action composed with the group projection and the continuous evaluation from
the root limit. Product continuity followed by subtype continuity gives the
claim.

`continuous_primeMonodromy_fixed` fixes the group coordinate.
`primeMonodromyContinuousLinearEquiv` uses this result at `g` and `g⁻¹`.
`primeMonodromyAction` is a locally installable `DistribMulAction` using this
same function; `primeMonodromyAction_continuousSMul` supplies its joint
continuity. No global action instance is installed.

## Compatibility with divisibility limits

For a selected predicate `P`, suppose all prime powers satisfy `P` and the
actual `mu` schemes are finite and étale at every positive selected index.
`toPrime_monodromy` says that `Divisibility.toPrime` intertwines selected
integral monodromy and the prime-adic monodromy constructed above. The latter's
finite étale families are obtained by evaluating the former families at
`Divisibility.primePowerIndex P p hP n`.

`fullToPrime_monodromy` gives the full-system specialization, using hypotheses
at every positive order. `awayToPrime_monodromy` gives the specialization for
orders coprime to an arbitrary natural modulus `m`, with the hypothesis
`Nat.Coprime p m`. It only requires finite étaleness at retained positive
orders. All three equalities are definitional: the two sides evaluate the
same finite geometric action at the same prime-power coordinates.

These maps and the existing full-to-away restriction therefore retain the
same geometric automorphism throughout the comparisons. No prime-product
isomorphism is asserted. Rational actions, path transport, identification
with an absolute Galois group, pairing equivariance, finite étaleness
theorems and completion of the PEL level construction remain separate work.
