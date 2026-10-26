# Imaginary determinant twists of whole-Levi analytic predicates

Author: Worker 429.

`Langlands.LeviImaginaryTwistModCenterStatement.{uF,uV}` is a closed
proposition. For every p-adic field `F`, compatible topological data `T`,
natural rank `n`, ordered block shape `B`, arbitrary complex representation
`σ` of `B.Levi F.Carrier`, and real vector `u`, it sets

```text
σu = Rep.of (T.leviComplexPowerTwist B
  (fun i => Complex.I * (u i : ℂ)) σ.ρ).
```

It asserts that `RelativeRegularComparison.IsLeviSquareIntegrable T B σu`
is equivalent to the same predicate for `σ`, and that
`RelativeRegularComparison.IsLeviTempered T B σu` is equivalent to the
same predicate for `σ`.

The twist retains the original carrier, complex module and field.
The field universe `uF` and representation-carrier universe `uV` are
independent. All natural ranks, including zero, are retained, and the
parameter is any real vector. There is no irreducibility, unitarizability,
tensor factorization, support, finite-dimension, positive-rank or
zero-sum premise.

The two existing analytic predicates are imported unchanged. Each
quantifies over every supplied measurable structure, proof of the Borel
property, and Haar measure on the actual quotient
`B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)` with the topology
supplied by `T`. Thus this is a statement on the whole product Levi modulo
its full center. The proposed equivalences compare the same measurable
structure and measure on their two sides. They retain admissibility,
the existence of a smooth unitary scalar central character, all
smooth-dual functionals and vectors, and the original `MemLp` requirements.
Temperedness retains every positive real epsilon in its exponent
`2 + ε`.

## Internal provenance and intended proof

This is an internal specialization of the published
`Langlands.UnitaryTwistModCenterStatement`, proved by
`Langlands.unitaryTwistModCenter` in `Twist.UnitaryModCenterProof`.
The proposed separate proof uses
`T.isOpen_ker_leviComplexPowerCharacter` and
`T.norm_leviComplexPowerCharacter_imaginary` from `Twist.LeviComplexPower`
to verify its two character hypotheses. It then applies the generic
equivalences to each measurable structure and Haar measure quantified
by the whole-Levi predicates. The same argument in each direction gives
the equivalences of the universally quantified predicates.

No external theorem or identification of a source's parameter space is
invoked: the complex vector in this statement is literally `i*u` in the
Library's existing determinant coordinates. No claim is made about
twisting by an arbitrary real determinant vector.

This file defines the proposition and proves neither equivalence.
Induced families, analytic continuation, persistence of selected
constituents, exponent cones, Jacquet multiplicity comparisons and
irreducible heads remain separate obligations in the supported
all-regular comparison.
