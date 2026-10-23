# Geometric monodromy on rational and adelic roots-of-unity twists

This internal construction extends the geometric action on the published
integral root limits to their existing rationalizations. It imports
`TwistIntegralMonodromy` and `TwistAwayRationalScalars`. The construction uses
their actual root carriers, geometric evaluation and scalar actions without
choosing roots, a basis or a trivialization. All declarations below belong to
`Langlands.TateTwist.Geometry`.

## Hypotheses and carriers

Fix a scheme `S`, a field `Ω`, a point `s : Spec Ω ⟶ S`, and the hypothesis
`hfin` that every finite étale cover has a finite fibre at `s`.
`FundamentalGroup s hfin` is the existing automorphism group of this actual
finite-fibre functor.

For a predicate `P : ℕ → Prop`, the selected positive indices form
`GroupScheme.Tate.Index P`. The named instance families `hμfin` and `hμet`
state that the structural maps of `mu S n.val` are finite and étale at all
these indices. These assumptions remain explicit. This module neither
derives them from invertibility of the orders nor imposes algebraic closure,
connectedness or local noetherianity; those belong to the intended geometric
application and its separate existence theorems.

The rational carrier is exactly
`Divisibility.Rational Ω P = ℚ ⊗[ℤ] Divisibility.Integral Ω P`.
The integral factor consists of coherent families of actual roots of unity.
For `P = True` this is the full rational twist. For
`P n = Nat.Coprime n m` it is the away twist, where `m` is any natural
modulus. It is not a tensor product over `ℤ` with the finite adèles.

## Rational action and representation

`rationalMonodromyMap` takes the integer-linear map underlying the published
`integralMonodromyHom` and extends scalars from `ℤ` to `ℚ`. The formula
`rationalMonodromyMap_tmul` is

```text
ρ(g)(q ⊗ x) = q ⊗ integralMonodromy(g)(x).
```

`rationalMonodromyMap_one` and `rationalMonodromyMap_mul` prove the left-action
laws by tensor induction. The pure-tensor cases use the integral action
laws; the additive cases use linearity. The product order is
`ρ(g * k)(x) = ρ(g)(ρ(k)(x))`.

`rationalMonodromy` bundles the resulting rational linear equivalence, whose
inverse is evaluation at `g⁻¹`. `rationalMonodromy_tmul` records the same
formula for the equivalence. `toRational_monodromy` shows that the existing
integral-to-rational map is equivariant; it makes no injectivity assertion.
`rationalRepresentation` bundles the action as a monoid homomorphism, and
`rationalMonodromyAction` supplies an optional local `DistribMulAction`.

## Full finite-adelic scalars

`rationalMonodromy_scalarAction` proves that rational monodromy commutes with
the existing action of `ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`. It applies
`TateScalarExtension.map_action` to the published
`integralMonodromyLinearEquiv`, which preserves the actual full residue
scalar action.

The finite-adelic constructions take the explicit proposition hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`. The existing
`Divisibility.finiteAdeleAction` transports rationalized residue scalars
through the comparison determined by `h`.
`rationalMonodromy_finiteAdeleAction` therefore follows from the rationalized
scalar compatibility. `finiteAdeleMonodromy` bundles this same geometric
action as a linear equivalence over `Global.FiniteAdeles ℚ`, using the
existing `finiteAdeleModule` locally. `finiteAdeleRepresentation` bundles
these equivalences and the same action laws. These definitions work for any
selected predicate and in particular for the full twist.

## Away specialization and restriction

`rationalFullMonodromy` specializes to all positive orders with full finite
étale hypotheses. `rationalAwayMonodromy` specializes to positive orders
coprime to `m`, using only those orders' hypotheses.
`rationalRestrictAway_monodromy` proves that the existing full-to-away map
intertwines these two actions. The away finite étale families are the
restrictions of the full families. Tensor induction reduces the equality to
the identical integral coordinate constructions.

`rationalAwayMonodromy_scalarAction` proves compatibility with
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m` using the published away
integral linear equivalence. The finite-adelic version retains
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
coupled to the same full comparison hypothesis `h`.
`rationalAwayMonodromy_primeToFiniteAdeleAction` shows preservation of the
existing away finite-adelic action. `primeToFiniteAdeleMonodromy` and
`primeToFiniteAdeleRepresentation` bundle the resulting equivalences and
representation over `Global.PrimeToFiniteAdeles m`.

## Scope and provenance

The derivation uses the actual integral geometric root action and the
published scalar-extension API. It follows the same tensor-extension
argument used for abelian-scheme Tate modules in `RationalMonodromy`, but
uses the roots-of-unity carriers and their explicit `mu` hypotheses.
No field automorphism or arbitrary action is substituted for geometric
fibre-functor evaluation.

This unit is algebraic: no topology or continuity theorem on these
rationalizations is asserted. It does not identify the fundamental group
with an absolute Galois group or prove the scalar-comparison hypotheses,
finite étaleness, a restricted-product comparison, path transport, pairing
equivariance or the completed PEL level construction.
