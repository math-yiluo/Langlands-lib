# Standard covariance of the actual adjacent Jacquet integral

This is an internal derivation from the exact normalized opposite-parabolic
induction, original-module tensor coordinates, scalar kernel and scalar integral
in `AdjacentRankNormalizedSection`, `AdjacentRankJacquetEvaluation` and
`AdjacentRankJacquetLinear`. It constructs the standard Whittaker functional
under an explicit all-section integrability premise. It does not discharge that
premise, prove nonvanishing or prove the host image equality.

The namespace is `Langlands.RankinSelberg.AdjacentJacquet`. All ranks include
`r = 0`. The p-adic field has its canonical topology, and its universe `uF` is
independent of the original complex module's universe `uV`. No topology or norm
is imposed on that module, and its specified Whittaker coefficient map need not
be injective. The scalar additive Haar `nu` is supplied by the caller, and no
self-duality premise is needed for this covariance result.

## Exact matrix algebra

For an ambient upper-unipotent element `n` of rank `r+2`, `unipotentHead n` is
its literal leading block of rank `r+1`, and `unipotentColumn n` is its last
column above the diagonal. Write these as `a` and `b`. The head is invertible
because it is upper triangular with every diagonal entry one;
`unipotentHead_mem` proves its upper unipotence.

`lowerBlock a` is the standard rank inclusion `diag(a,1)`.
`lowerBlockParabolic a` proves membership in the host's exact lower parabolic
with ordered blocks `(r+1,1)`, and its large Levi projection is exactly `a`.
The four entry formulas also prove that this embedding preserves upper
unipotence. Direct finite matrix multiplication gives

```text
n = upperColumn b * lowerBlock a,
upperColumn x * n = lowerBlock a * upperColumn (a^(-1) * (x+b)).
```

Here `upperColumn x` is precisely the actual matrix `[I,x;0,1]` from
`AdjacentRankJacquetEvaluation`. The corresponding substitution is
`unipotentShift n x`. An upper-unipotent head fixes the last coordinate of a
column, so

```text
(unipotentShift n x)_last = x_last + b_last.
```

Splitting the finite first-superdiagonal sum into its leading terms and its
last term gives `standardCharacter_split`:

```text
theta_(r+2)(n) = theta_(r+1)(a) * psi(b_last).
```

These statements use the actual `Fin` indices of the host shapes, without
changing the ordered carrier or assuming a positive lower bound on `r`.

## The supplied Haar and lower covariance

`measurePreserving_unipotentShift` factors the shift into translation by `b`
and column multiplication by `a^(-1)`. Translation preserves the supplied
product additive Haar. The proved column pushforward formula
`AdjacentDoubleIntegral.rowMeasure_map_mulVec` scales this same measure by
`|det(a^(-1))|^(-1)`, which is one by upper unipotence. The same factorization
through a column homeomorphism proves `measurableEmbedding_unipotentShift`.
Thus subsequent integration retains the caller's Haar normalization.

`tensorCoordinates_lowerBlock_action` applies the intertwining identity for
`Padic.adjacentRankLowerInducingCoordinates`. On `diag(a,1)` with upper-unipotent
`a`, both the ambient and leading determinant weights are one. The normalized
inducing action, after the original tensor coordinates, is therefore exactly
`sigma(a)` on the original module. Applying induction covariance and then the
specified standard Whittaker functional `ell` gives
`sectionCoefficient_lowerBlock`:

```text
sectionCoefficient f (diag(a,1)*g)
  = theta_(r+1)(a) * sectionCoefficient f g.
```

This proves covariance directly for the canonical normalized induction used by
the host. No identification with a faithful coefficient-model induction is
assumed.

## The scalar kernel and common functional

The imported literal kernel is

```text
integrand f g x = sectionCoefficient f (upperColumn x * g) * psi(-x_last).
```

`integrand_unipotent_mul` combines the matrix factorization, lower covariance,
last-coordinate identity and character splitting to prove

```text
integrand f (n*g) x
  = theta_(r+2)(n) * integrand f g (unipotentShift n x).
```

The phase calculation uses
`psi(b_last) * psi(-(x_last+b_last)) = psi(-x_last)`. Thus the result uses the
standard ambient character with the imported negative Jacquet phase.
`integral_unipotent_mul` integrates this identity, factors out the complex
constant and applies the proved measure-preserving measurable substitution.
This identity holds for totalized scalar Bochner integrals and does not itself
assert absolute convergence.

The selected definition `functional` assumes the explicit hypothesis

```text
hI : for every actual induced section f and every ambient g,
     Integrable (integrand f g) (rowMeasure nu (r+1)).
```

The already proved `integralLinear` then supplies a linear functional by
integration at the identity. Right translation identifies its evaluation on
`rho(n)f` with the integral at `n`. The preceding covariance theorem proves
that this functional belongs to `glFunctionals psi (r+1) rho` for the exact
host induction `rho`. Finally, `functional_coefficient` proves for every
actual section `f` and every ambient group element `g` that

```text
(functional nu hI).val (rho(g)f) = integral nu f g.
```

This is a single original-carrier functional with all its coefficients given
by the literal Jacquet integral. Its possible nonzero value, discharge of
`hI`, sufficiently large real-twist specialization and equality with the whole
tensor-integral image remain obligations of the host proof. The current
construction uses only scalar integration and elementary matrix and character
identities on the already constructed exact induction; it imports no later
adjacent-rank analytic base or unrestricted multiplicativity theorem.
