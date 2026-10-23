# Rational prime-adic multiplicative Tate base change

This internal construction extends the actual integral prime-adic
multiplicative Tate comparison from the p-adic integers to the p-adic
field. It also proves compatibility with rational prime extraction,
restriction of test schemes and affine root coordinates. The namespace
is `Langlands.GroupScheme.Gm.TateComparison`.

## Inputs and provenance

Let `b : S' ⟶ S` be a morphism of schemes in the same universe,
`T : Over S'` a test scheme, and `p : ℕ` a prime, expressed as
`[Fact p.Prime]`. The actual rational prime-adic Tate module is

```text
Tate.PrimeAdic.Rational (Gm S').toGrp T p
  = ℚ_[p] ⊗[ℤ_[p]] Tate.PrimeAdic.Integral (Gm S').toGrp T p.
```

The imported `primeIntegralBaseChange` is a continuous
`ℤ_[p]`-linear equivalence whose every coordinate is identified with
actual torsion pullback after `(Gm.baseChangeIso b).inv`. This file
extends that equivalence over `ℤ_[p]`, using `LinearEquiv.baseChange`.
The rational extraction maps come from `RationalPrime` and their
semilinear bundles from `RationalPrimeScalars`; the twist scalar-tower
instances are imported from `TwistRationalPrime`. The other inputs are
the existing actual test restrictions and canonical affine comparison.
All claims are derived from those constructions; no new external
literature assertion is made.

## Comparison and rational roots

`primeRationalBaseChange b T p` is the `ℚ_[p]`-linear equivalence
from the displayed module to
`Tate.PrimeAdic.Rational (Gm S).toGrp ((Over.map b).obj T) p`.
It scalar-extends the linear equivalence underlying
`primeIntegralBaseChange b T p`. The formula
`primeRationalBaseChange_tmul` sends `q ⊗ x` to
`q ⊗ primeIntegralBaseChange b T p x`.
`primeRationalBaseChange_toRational` states compatibility with the
canonical integral-to-rational maps `x ↦ 1 ⊗ x`. Both are definitional.

`primeRationalEquiv_primeRationalBaseChange` proves

```text
primeRationalEquiv ((Over.map b).obj T) p
    (primeRationalBaseChange b T p x)
  = primeRationalEquiv T p x.
```

The common target is the rational actual roots-of-unity twist of
`Γ(T.left, ⊤)`: composition with `b` preserves the underlying test
scheme and its global section ring. The proof establishes equality of
the two linear maps using `TensorProduct.AlgebraTensorModule.ext`,
reduces a pure tensor to the integral root-coordinate identity, then
evaluates that map equality at `x`.

## Rational prime extraction

For `P : ℕ → Prop` and `hP : ∀ n : ℕ, P (p ^ n)`, the theorem
`rationalToPrime_rationalBaseChange` states that the square

```text
Rational(Gm S', T, P) ── rationalBaseChange ──▶ Rational(Gm S, T over S, P)
       │ rationalToPrime                              │ rationalToPrime
       ▼                                              ▼
PrimeAdic.Rational(Gm S', T, p) ── primeRationalBaseChange ──▶
                                      PrimeAdic.Rational(Gm S, T over S, p)
```

commutes. Here `T over S` denotes `(Over.map b).obj T`. The vertical
maps are the existing rational-linear extraction maps, sending
`q ⊗[ℤ] x` to `(q : ℚ_[p]) ⊗[ℤ_[p]] toPrime x`. The horizontal
maps therefore use different scalar-extension bases, as required.
Tensor induction on the source reduces the pure-tensor square to
`toPrime_integralBaseChange`; sums follow from additivity.

`rationalToPrimeSemilinear_rationalBaseChange` gives the same equality
for the existing semilinear extraction, whose underlying function is
identical. The full specialization
`rationalFullToPrime_rationalBaseChange` uses the always-true predicate.
For any natural modulus `m` and `h : Nat.Coprime p m`, the theorem
`rationalAwayToPrime_rationalBaseChange` uses the predicate of orders
coprime to `m` and the proof `h.pow_left n` for every p-power.
`rationalAwayToPrimeSemilinear_rationalBaseChange` gives its semilinear
version. These specialization proofs reuse the general square. No
primality or nonzero hypothesis on `m`, and no bijectivity of an
extraction map, is asserted.

## Test restriction and affine specialization

For any test-scheme morphism `a : T' ⟶ T` over `S'`, the theorem
`primeRationalBaseChange_testRestrict` states that restriction before
base change at `T'` equals restriction along `(Over.map b).map a`
after base change at `T`. The restriction is the actual
`Tate.PrimeAdic.rationalTestRestrict`. The proof establishes equality
of the composed linear maps by tensor extensionality and the integral
test-restriction square, then evaluates at the given element.

For `R : CommRingCat` and `t : Spec R ⟶ S'`, the abbreviation
`primeRationalBaseChangeAt b p t` compares the modules at `t` and
`t ≫ b`. The theorem
`affinePrimeRationalEquiv_primeRationalBaseChangeAt` says that these
elements have equal images in `TateTwist.Rational R p`. Again tensor
extensionality reduces to the integral affine identity, which uses the
canonical Gamma-Spec isomorphism. Fields, including geometric-point
fields, are special cases.

## Scope

The comparison is algebraic. No rational topology or continuity,
compactness, finite étaleness, rank, restricted-product identification,
monodromy pullback, pairing compatibility or identity/composition law
for iterated base change is claimed by this file. Arbitrary schemes
and test schemes are allowed; no invertibility assumption is needed
for these comparison identities. The geometric content is inherited
from the integral comparison's actual finite-coordinate formula. No
roots, basis or twist trivialization is chosen, and this unit does not
complete the parent PEL task.
