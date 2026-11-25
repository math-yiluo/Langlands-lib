# Conditional conversion of the real Rankin–Selberg conventions

This is an internal reduction, with an implemented proof,
to three named premises. Its conclusion is exactly the Library statement
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement.{u}`.
It does not prove that conclusion unconditionally.

The entry proposition is
`RealPlaceJacquetConventionReductionStatement`; its proof is
`realPlaceJacquetConventionReduction`. All names below are in
`Langlands.Global.RankinSelbergGlobal`, with the helper namespace `RealJacquet`
where indicated.

## Provenance and scope

The motivating original source is Hervé Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, SHA256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
PDF pages equal printed pages. Page 3 specifies the negative Fourier kernel and
the Casselman–Wallach setting. Pages 4–5 describe induced representations,
Whittaker functions and dual functions. Page 5 describes the negative-kernel
rank-one equation and additive-character scaling. Theorem 2.1 on page 6 gives
convergence, continuation and the rank-dependent functional equations;
page 7 identifies parameter determinants with central characters. These pages
were read from the registered original PDF.

This module is a derived formal organization of the convention conversion. It
is not a direct formalization of Jacquet's proof or a proof that his theorem
applies to the Library's global restrictions. In particular, the premise below
expresses the desired source-convention equation using the Library epsilon at
`-a`; the analytic theorem, model membership, and identification of all these
normalizations remain part of that premise. No analytic theorem is inferred
from the source citation alone.

The module imports the Library's
`ArchimedeanFunctionalEquationStatement` and Mathlib tactics. It changes neither
the Library target nor its dependencies. The module was checked with Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

## The three retained premises

`RealJacquetRestrictionEquationStatement` has an unequal-rank conjunct and an
equal-rank conjunct. Both retain the Library target's complete global data:
a number field with compact additive adelic quotient; a unitary additive
character trivial on the field; the four actual cuspidal realizations and their
contragredience hypotheses; the real place and its additive component `a`;
the four lists of real parameter blocks with `HasRealPlaceParameter`; all
quotient measure data `D`; and the two actual global Whittaker restrictions.
The equal-rank conjunct also quantifies over every Schwartz function, including
rank `r = 0`.

Write `c = realMinusOneScalar T v` and `d = realMinusOneScalar T' v`.
In unequal ranks the premise uses the target's actual integral, dual block
kernel, rectangular measure and dual integral, but its epsilon parameter is
`-a` and its sign is `c^(t+1) * d`. In equal ranks the dual Fourier transform is
`realFourierTransform (-a)`, the epsilon parameter is `-a`, and the sign is
`c^r`. In both cases the positive epsilon measure scale stays
`NNReal.sqrt ‖(a : ℝ)‖₊`. Thus the open input retains convergence of both
kernels, holomorphy of both integrals, meromorphic continuation with half-plane
agreement, and the equation off a discrete set. It also retains the substantive
work of placing arbitrary global restrictions in suitable local Whittaker
models. `HasRealPlaceParameter` is not treated as that membership theorem.

`RealPairCentralCompatibilityStatement` states, for every actual pair of
cuspidal realizations with real parameters, that

```
(RealJacquet.determinant (realPairBlocks ds es) (-1) : ℂ)
  = c^(t+1) * d^(r+1).
```

Here `RealJacquet.determinant` is explicitly the product of the block
determinant multipliers. This premise retains both the tensor-parameter
comparison and its compatibility with the compact-action scalar. The module
does not prove existence of a scalar action or the general determinant formula
for tensor products.

`RealEqualDualReflectionStatement` uses all the equal-rank global hypotheses
above and asserts two facts for every spectral value: integrability of the
negative-Fourier dual kernel is equivalent to integrability of the
positive-Fourier dual kernel, and

```
realEqualDualIntegral (-a) D W W' Φ s
  = (c * d) * realEqualDualIntegral a D W W' Φ s.
```

This is a separate input; the Library proves it as `realEqualDualReflection`
(module `RealPlaceEqualReflection`). Invariance of the quotient measure under
reflection, covariance of the Whittaker restrictions under the central element,
and the resulting integral change of variables are not proved here.

## Unconditional helpers

`RealJacquet.realSign_neg`, `realToComplex_neg` and `block_determinant_neg`
prove multiplicativity under negation directly from the explicit characters.
`block_epsilon_neg` expands the Library's block epsilon formula; absolute
values do not change under negation. List induction then proves `epsilon_neg`
and its pair specialization `pair_epsilon_neg`:

```
epsilon(ds, -a, c₀, s) = determinant(ds, -1) * epsilon(ds, a, c₀, s).
```

The same positive Haar scale `c₀` appears on both sides. No presentation
independence or Weil-representation comparison is asserted by these lemmas.

`selfDualMeasure_neg` is equality of the actual defined additive Haar measures.
`fourier_neg` uses this equality and pointwise equality of the character kernels
to show, for every function without regularity assumptions,

```
realFourierTransform (-a) Φ x = realFourierTransform a Φ (-x).
```

This helper explains the reflection input but does not discharge it.

`representation_scalar_sq` proves that a scalar action of an involutive group
element on a nonzero complex representation has square one. Apply the action
twice to a nonzero vector and cancel scalar multiplication. The wrapper
`realMinusOneScalar_sq` applies this to `-1` in the actual real compact group.
When a scalar action exists, the Library's choice specification identifies it;
when it does not, the defined fallback scalar is one. Thus the square identity
is unconditional, but it does not assert that the fallback acts as a scalar.

The ring identities `unequal_sign` and `equal_sign` use only `c² = d² = 1`.
They prove, respectively,

```
(c^(t+1) * d) * (c^(t+1) * d^(r+1)) = d^r,
(c * d) * (c^r * (c^(r+1) * d^(r+1))) = d^r.
```

## Implemented reduction proof

`RealJacquet.EquationPackage` collects the target's two integrability clauses,
two holomorphy clauses, two meromorphic functions, two half-plane agreement
clauses, and the multiplied-out equation in the codiscrete filter. The integral
functions and kernels are separate arguments, accommodating the iterated dual
block integral. `UnequalEquation` and `EqualEquation` specialize this package
to the actual Library real-place integrals and pair factors.

`EquationPackage.change_factor` changes only the sign-times-epsilon expression
using its supplied pointwise identity. All analytic data are reused.
`EquationPackage.reflect_dual` takes the stated integrability reflection and
integral equality `Zn = k * Zp`, with `k² = 1`. It uses `k * Md` for the new
dual meromorphic continuation. Multiplication by a constant preserves
holomorphy and meromorphy, and the original equation is multiplied by `k`.
The positive continuation is unchanged.

In unequal ranks the main proof applies `change_factor` to the restriction
premise. `pair_epsilon_neg`, central compatibility and `unequal_sign` give the
exact target sign `d^r`. In equal ranks it first applies `reflect_dual` with
`k = c * d`; its square is one by `realMinusOneScalar_sq`. It then applies
`change_factor`, using `pair_epsilon_neg`, central compatibility and
`equal_sign`. The resulting two packages are definitionally the Library's
unequal and equal statements. The universe remains free and every original
binder, including all quotient measures and the equal-rank base case, is
preserved. The three premises remain explicit hypotheses of the proved
implication.
