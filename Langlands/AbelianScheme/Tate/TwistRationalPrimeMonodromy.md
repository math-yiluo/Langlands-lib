# Geometric monodromy on rational prime-adic roots-of-unity twists

This internal construction extends the published prime-adic integral root
monodromy to the existing rational prime-adic twist and proves equivariance
of the published rational extraction maps. It imports `TwistPrimeMonodromy`,
`TwistRationalMonodromy`, and `TwistRationalPrimeScalars`. All declarations
below belong to `Langlands.TateTwist.Geometry`.

## Hypotheses and carriers

Fix a scheme `S`, a field `Ω`, a point `s : Spec Ω ⟶ S`, and
`hfin : ∀ Y : Cover S, Finite (Fiber s Y)`. The acting group is the existing
`FundamentalGroup s hfin`, defined as the automorphism group of the actual
finite-fibre functor.

For a natural prime `p`, expressed by `[Fact p.Prime]`, the local construction
requires named instance families `hμfin` and `hμet` asserting that the
structural maps of the actual schemes `mu S (p ^ n)` are finite and étale
for every natural `n`. This includes `n = 0`, whose order is one. These
hypotheses remain explicit. No algebraic closure or connectedness assumption
is needed for this conditional construction; the module does not establish
the finite étaleness hypotheses from invertibility of the orders.

The carrier is exactly the published
`TateTwist.Rational Ω p = ℚ_[p] ⊗[ℤ_[p]] TateTwist.Integral Ω p`.
The integral factor is the existing limit of coherent actual prime-power
roots of unity. The existing additive and `ℚ_[p]`-module structures are
retained. The action uses geometric evaluation from `TwistPrimeMonodromy`;
no arbitrary action, compatible roots, basis, or twist trivialization is
supplied as data.

## Scalar extension and action laws

`rationalPrimeMonodromyMap` applies `LinearMap.baseChange ℚ_[p]` to the
published `primeMonodromyHom`, extending its scalars from `ℤ_[p]` to
`ℚ_[p]`. The formula `rationalPrimeMonodromyMap_tmul` is

```text
ρ(g)(q ⊗ x) = q ⊗ primeMonodromy(g)(x).
```

Here `q : ℚ_[p]`, and the tensor product is over `ℤ_[p]`.
`rationalPrimeMonodromyMap_one` and `rationalPrimeMonodromyMap_mul` prove
identity and the left-action law
`ρ(g * k)(x) = ρ(g)(ρ(k)(x))`. Their proofs first express the published
integral action laws as equalities of linear maps, apply scalar extension,
and use `LinearMap.baseChange_id` and `LinearMap.baseChange_comp` before
evaluating at `x`.

`rationalPrimeMonodromy` bundles the resulting `ℚ_[p]`-linear equivalence.
Its inverse is the same construction at `g⁻¹`; the action laws verify both
inverse identities. `rationalPrimeMonodromy_tmul` records the same formula
for this equivalence. `rationalPrimeRepresentation` packages these
equivalences and laws as a monoid homomorphism.
`rationalPrimeMonodromyAction` is an optional locally installed
`DistribMulAction` using the identical function, not a global instance.

`primeToRational_monodromy` says that the existing map
`TateTwist.toRational Ω p`, given by `x ↦ 1 ⊗ x`, intertwines integral and
rational prime-adic monodromy. Its proof is reflexivity. No injectivity of
this map is asserted.

## Rational extraction compatibility

For a predicate `P : ℕ → Prop`, selected indices are the positive integers
in `GroupScheme.Tate.Index P`. The selected comparison requires finite
étaleness of the actual `mu S n.val` at all such indices and
`hP : ∀ n : ℕ, P (p ^ n)`. The prime-power finite étale families in the
conclusion are obtained from these same families using
`Divisibility.primePowerIndex P p hP`.

`rationalToPrime_monodromy` states

```text
rationalToPrime (rationalMonodromy(g)(x))
  = rationalPrimeMonodromy(g)(rationalToPrime(x)).
```

The source is the existing
`Divisibility.Rational Ω P = ℚ ⊗[ℤ] Divisibility.Integral Ω P`.
The existing extraction map is rational-linear and sends `q ⊗ x` to
`(q : ℚ_[p]) ⊗ Divisibility.toPrime Ω P p hP x`. Thus source and target
retain their different scalar-extension base rings. Tensor induction on
the source reduces the proof to the published integral
`toPrime_monodromy`; the pure-tensor case applies the tensor function to
that equality, and additivity proves the sum case.

`rationalToPrimeSemilinear_monodromy` gives the same pointwise identity for
the existing semilinear projection over
`Global.ProfiniteIntegerRing.rationalToPadic p`. It follows from the
identity of this projection's underlying function with `rationalToPrime`.
In particular it also applies to the full specialization of that map.

`rationalFullToPrime_monodromy` specializes to `P = True`, using explicit
finite étale hypotheses at every positive order and the existing
`rationalFullMonodromy` and `rationalFullToPrime`.

For any natural modulus `m` and `h : Nat.Coprime p m`,
`rationalAwayToPrime_monodromy` specializes to the positive orders coprime
to `m`. It uses only finite étaleness at those retained orders; the witness
`h.pow_left n` retains every prime power. The actions and projection are
the existing `rationalAwayMonodromy` and `rationalAwayToPrime`.
`rationalAwayToPrimeSemilinear_monodromy` states the same identity for the
away semilinear projection over
`Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h`.
Both full and away identities follow by specialization of the selected
identity, and the away semilinear identity reuses its underlying function.

## Provenance and scope

This is an internal derivation from published geometric root actions and
rational extraction maps, using Mathlib's scalar-extension functoriality.
The implemented proofs are described above; no new claim is attributed to
external literature. The same geometric automorphism is retained across
all comparisons, without an identification with a field Galois group.

The construction is algebraic. It introduces no topology or continuity
claim on a rational twist, no comparison isomorphism with a restricted
product, no new finite-adele scalar comparison, and no injectivity or
surjectivity assertion for extraction. Path transport, finite-etaleness
theorems, pairing equivariance and completion of the PEL level structure
remain separate obligations.
