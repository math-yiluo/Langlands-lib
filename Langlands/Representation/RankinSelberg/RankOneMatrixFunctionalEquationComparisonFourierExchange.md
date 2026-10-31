# Actual bilinear matrix Fourier exchange

This internal prerequisite proves a bilinear identity for the actual
plus-sign rectangular Fourier integral and its transport by two
determinant-norm-one left factors. It does not prove the weighted unipotent
exchange, integration against a Whittaker model, or the final matrix-to-rank-one
gamma comparison.

For a field `K` with a topological ring structure, a Borel measurable structure
and second countable topology, let `ψ` be a unitary additive character and
`ν` a supplied additive Haar measure whose scalar measure is sigma finite.
The rectangular sizes `r,s` are arbitrary natural numbers, including zero.
Write `μ = RankinSelberg.rectangularMeasure ν r s`, the actual nested product
measure on `r × s` matrices, and `Fψ,ν` for
`rectangularFourierIntegral ψ ν`.

`rectangularPairing_comm` proves symmetry of the entry pairing by commutativity
of scalar multiplication. `rectangularFourierExchangeKernel ψ Φ Ψ` is the
literal function

```text
k(X,Y) = Φ(X) Ψ(Y) ψ(sum_i sum_j X_ij Y_ij).
```

For any two Schwartz–Bruhat tests `Φ,Ψ`,
`rectangularFourierIntegral_exchange` proves integrability of each of
`Fψ,ν(Φ)(X) Ψ(X)` and `Φ(X) Fψ,ν(Ψ)(X)` under `μ`, together with

```text
∫ Fψ,ν(Φ)(X) Ψ(X) dμ(X) = ∫ Φ(X) Fψ,ν(Ψ)(X) dμ(X).
```

The proof first integrates the compactly supported continuous tests. Their
product on the product space is integrable. The continuous kernel has exactly
that product's norm because `ψ` has norm one, so it is integrable as well.
Fubini then supplies integrability of both iterated integrals and their
equality. Symmetry of the entry pairing identifies the two inner integrals
with the displayed Fourier expressions. This is a bilinear identity without
complex conjugation; it does not use Fourier inversion or self-duality.

`padicRectangularFourierIntegral_exchange_left` specializes to any
`F : PadicField p` with prime `p` and any supplied `T : F.TopologicalData`.
Its telescope installs `T.topology` and the scalar Borel measurable structure.
It quantifies over every `ψ`, every supplied additive Haar `ν`, any
`A,B : GeneralLinear r F.Carrier` satisfying
`T.determinantNorm r A = T.determinantNorm r B = 1`, and any tests `Φ,Ψ`.
It proves integrability of both displayed products and the equality

```text
∫ Fψ,ν(Φ)(B X) Ψ(A X) dμ(X)
  = ∫ Φ(X) Fψ,ν(Ψ)(iota(A B⁻¹) X) dμ(X),
```

where `iota` is the actual `GeneralLinear.inverseTranspose`.
The proof applies the first exchange theorem to `Φ` and the pullback
`ΨD(X)=Ψ(D X)` with `D=A B⁻¹`. The existing actual Fourier transport theorem
identifies its transform with evaluation at `iota(D) X`. The existing
measure-preserving left-right theorem permits the substitution `X ↦ B X`.
The determinant-norm-one hypotheses remove the Haar scalar in both steps.
The same `ν` occurs throughout, with no normalization or self-duality
assumption. Local-field sigma compactness supplies scalar sigma finiteness.

The provenance is derived: the proof combines the Library's concrete
rectangular Fourier definition, Schwartz test continuity and compact support,
the unit norm character identity, Mathlib's Bochner Fubini theorem, and the
published actual determinant-norm-one Fourier transport results in
`RankOneMatrixFunctionalEquationComparisonFourierTransport`. No literature
assertion or unproved analytic comparison is used as a premise.
