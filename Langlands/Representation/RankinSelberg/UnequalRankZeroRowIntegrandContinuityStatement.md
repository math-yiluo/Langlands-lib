# Continuity of the zero-row unequal-rank quotient integrand

`Langlands.RankinSelberg.UnequalRankZeroRowIntegrandContinuousStatement.{uF,uV,uW} F n k`
is an internal proposition asserting continuity of the actual zero-row
unequal-rank JPSS integrand on the left-unipotent quotient
`N_(n+1) \ GL_(n+1)(F)`. The field `F` carries an arbitrary topology with
continuous ring operations. The small rank is `n + 1` and the large rank is
`n + (0 + k + 1) + 1`, so the gap is the positive number `k + 1`. Both `n = 0`
(rank one) and `k = 0` (gap one) are included.

## Statement

For every real absolute value `abv` on `F` that is continuous, the proposition
quantifies over:

- independent complex vector spaces `V : Type uV` and `W : Type uW`, with no
  topology on either;
- representations `π` of `GL_(n+(0+k+1)+1)(F)` on `V` and `σ` of `GL_(n+1)(F)`
  on `W`, both smooth (`IsSmooth`);
- a unitary additive character `ψ`, a standard Whittaker functional
  `ℓ : glFunctionals ψ (n + (0 + k + 1)) π` and an inverse-character functional
  `ℓ' : glInverseFunctionals ψ n σ`;
- elements `f` and `f'` of the actual coefficient images
  `(coefficientModel π ℓ).toSubmodule` and `(coefficientModel σ ℓ').toSubmodule`;
- a complex number `s`.

The conclusion is exactly

```text
Continuous (unequalRankIntegrand ψ abv 0 k f.val f'.val s 0).
```

Here `unequalRankIntegrand` is the published integrand on the published left
quotient, with its quotient topology. The final `0` is the unique matrix in the
zero-row space `Matrix (Fin 0) (Fin (n + 1)) F`. On a representative `g`, the
integrand is

```text
f.val (unequalRankMatrix 0 k g 0) * f'.val g * |det g|^(s - (k+1)/2),
```

where the published lemma `unequalRankMatrix_zero_rows` identifies the matrix as
`appendIdentity n (0 + k + 1) g = diag(g, I_(k+1))`. The determinant weight is
`determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)`, the complex power of
the real number `abv (det g)`.

No nonzero, irreducibility, admissibility, finite-generation, Whittaker-type,
unitarity, central-character, torus-expansion, Iwasawa, Mellin, convergence or
rationality hypothesis is imposed. Zero functionals and zero coefficients are
allowed, as are smooth reducible representations. The supplied field topology is
used throughout; no particular topology is selected.

## Provenance

The motivation is the zero-row case `j = 0` of the unequal-rank integrals
`Ψ(s, W, W'; j)` in Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (Amer. J. Math. 105 (1983)), registered as
`jpss-1983-rankin-selberg`. In the proof of Theorem 2.7 (printed pp. 391–394)
the case `r > t` reduces to finitely many integrals of the form of display (7)
on printed p. 394,

```text
∫_(N_t \ G_t) W[diag(g, 1_(r-t))] W'(g) |det g|^(s-(r-t)/2) dg,
```

with `W ∈ W(π; ψ)` and `W' ∈ W(π'; ψ̄)`. In the Lean statement `t = n + 1` and
`r - t = k + 1`. The original source does not state this continuity proposition.
The formal interface, with its general topological field, explicit continuous
absolute value and coefficient-model vectors, is internal and derived from
published Library definitions. It should not be read as a verbatim statement from
JPSS.

The interface matches the continuity helper in Worker 331's private zero-row
analytic draft for task `d76b5b0f-33ec-486d-881e-b4c1e3494d40`. It is the
unequal-rank zero-row companion of the published equal-rank proposition
`Langlands.RankinSelberg.EqualRankIntegrandContinuousStatement`.

## Why the proposition is expected to hold

This module states the proposition only; it contains no proof. The intended
derived argument is a continuity adapter.

1. A coefficient-model vector is a matrix coefficient `g ↦ ℓ(π(g)v)` of a
   smooth vector, so it is locally constant on the general linear group and in
   particular continuous. The same holds for `f'`.
2. The embedding `appendIdentity n d`, sending `g` to `diag(g, I_d)`, is
   continuous: its matrix entries are entries of `g` or constants, and its
   inverse is the embedding applied to `g⁻¹`.
3. The determinant is continuous. Since `det g` is a unit, `abv (det g)` is
   strictly positive. On the positive reals the complex power with a fixed
   exponent is continuous, so the determinant weight is continuous.
4. The product is continuous on `GL_(n+1)(F)` and invariant under left
   upper-unipotent translation. The projection onto the left quotient is an open
   quotient map, published as `leftQuotient_isOpenQuotientMap`. Hence the
   descended integrand is continuous.

Continuity on the quotient gives measurability for the Borel structure used in
the analytic statements. This module does not prove convergence, rationality or
any integral interchange.

## Arbitrary p-adic topology specialization

Downstream p-adic statements use a prime `p`, a `PadicField F` and an arbitrary
supplied `T : F.TopologicalData`, not only a canonical one. To apply this
proposition at `F.Carrier`, install `T.topology`, `T.valuativeRel` and
`T.localField`; the required `IsTopologicalRing F.Carrier` instance is then
inferred. Take `abv = normalizedAbsoluteValue T`. Its continuity is

```text
NNReal.continuous_coe.comp T.continuous_normalizedAbsHom.
```

Applying the proposition to this absolute value gives continuity of
`unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0` for
every smooth `π` and `σ`, functionals, coefficient-model vectors and `s`. This is
the exact arbitrary-`T` form needed by Worker 331's zero-row analytic assembly
and by Worker 394's quotient measurability argument. The specialization does not
restrict `T` to a canonical choice.
