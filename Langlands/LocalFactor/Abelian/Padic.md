# Rank-one rational L-factors and convergent epsilon expressions

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Abelian.Padic`.
It is moved from `Langlands.LocalFactor.PadicAbelian` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. The uniformizer-unit declarations are now implemented in
[LocalField/Uniformizer](../../LocalField/Uniformizer.md), preserving their public
names, types and bodies; this module imports them. Original source references
and authorship below are retained.
The [migration record](Definitions.md#structural-migration-record) gives the complete map and checks.


Worker 33 authored the callable spectral expressions, conductor predicates and
their identification with the constructed conductors. Worker 20 reconciled
these with `LocalFactor.Abelian.Definitions`, proved convergence of the spectral Gauss
integral and equality of the unshifted constants, and added rational L-factors,
restricted evaluation and the conditional self-dual normalization wrappers.
Both authors must be retained on submission.

This construction belongs to one coherent contribution with `Conductor` and
`Abelian`, using the published harmonic prerequisite. It does not construct a
nonabelian constant system or prove a functional equation.

## Inputs and callable expressions

The namespace is `Langlands.LocalFactor.PadicAbelian`. The prime, finite
p-adic extension and carrier universe are arbitrary. Every construction uses
the explicit supplied `T : F.TopologicalData`, its actual discrete valuation,
integer ring, residue cardinality `q`, and normalized absolute value
`q^(-ord(x))`. Character types are the shared continuous quasicharacters and
nontrivial unitary additive characters. `BorelMeasure` abbreviates Mathlib's
measure type with the supplied topology's Borel measurable space; it introduces
no competing measure structure.

The callable expressions retain Worker 33's theorem interfaces:
`integerRing`, `integralUnits`, `spectralVariable`, `characterExtension`,
`lFactorAt`, `RegularPoint`, `ConvergesAt`, `zetaIntegrand`, `zeta`,
`ExtendsIntegral`, `laurentEvaluation`, `gaussIntegrand`, `gaussShell`,
`epsilonAt`, `lFactor`, `epsilon`, `deligneConstant` and `centeredConstant`.
The actual spectral variable is `exp(-s log q)`. The annulus has order
`-(n+a)`. At the specified conductor levels the unramified epsilon expression is

```
chi(pi)^n * exp(n * (1-s) * log q) * vol(O).
```

The ramified expression is the actual additive-Haar integral over that annulus
of `chi(x)^(-1) * exp(-s log |x|) * psi(x)`. The sign of the additive character
is positive. `epsilon` uses the constructed conductor values, not supplied
existence certificates. `uniformizerUnit` uses the already specified
uniformizer, with its nonzero and order-one properties proved.

`ConductorAt` and `AdditiveConductorAt` express the least and greatest
triviality levels used by the companion theorem target.
`unitLevel_iff_mem_principalUnits` identifies the former filtration with the
owner's actual subgroups, including level zero. At positive levels the
ultrametric equality for unequal valuations proves that every element
congruent to one is an integral unit. `conductorAt_iff` and
`additiveConductorAt_iff` use uniqueness of least and greatest elements to
identify those predicates with the actual constructed conductors. They assume
no conductor-existence theorem.

## Rational L-factor and evaluation

`lPolynomial` is the actual polynomial `1 - chi(pi) X` when the character is
unramified and the polynomial `1` otherwise. Its constant term is proved to
be one, hence it is nonzero. `rationalLFactor` is its reciprocal in `RatFunc C`;
its nonzero property and inverse identity are proved.

`regularPoint_iff_polynomial_ne_zero` proves that the existing regular-point
predicate is exactly nonvanishing of this denominator at `q^(-s)`.
`regularLValue` returns a complex unit only on that subtype. Its value agrees
with the raw `lFactor` expression there. Thus poles remain part of the rational
factor and are excluded from finite numerical evaluation.

`lFactorAt` and `lFactor` remain raw, totalized formula representatives to
preserve the companion statement interface. A totalized zero at a denominator
zero is not claimed to be an analytic value. The rational object, rather than
those raw values at poles, is the constructed L-factor. Normal-meromorphic
continuation of the zeta integral remains an explicit proposition;
`ExtendsIntegral` neither assumes nor selects a continuation.

## Convergence and identification of the constants

`characterExtension_eq_extendZero`, `integerRing_eq` and
`gaussShell_eq_valuationShell` identify the two presentations with the actual
objects from `Abelian`. The shell equality uses nonvanishing of the valuation
away from zero and the inverse exponential/logarithm identities in its
discrete value group.

On a shell of order `-d`, the normalized absolute value is exactly `q^d`.
`gaussIntegrand_on_shell` therefore expresses the spectral integrand as a
constant multiple of the unshifted integrand.
`gaussIntegrand_integrable` proves convergence for every complex `s`, every
integer shell and every actual regular additive Haar measure. It uses the
proved compactness and measurability of the shell and continuity of the
inverse-character integrand away from zero. The integral's use here does not
rely on the Bochner integral's fallback for nonintegrable functions.
Raw `zeta`, which integrates over the whole field, still requires the separate
half-plane convergence theorem.

`deligneConstant_eq_abelianEpsilonExpression` proves that the spectral
expression at zero is the previously constructed measure-dependent abelian
constant. In the ramified case this follows from the shell and integrand
identifications. In the unramified case the proof applies the existing
scale-independence theorem to `pi^n`, proves its valuation and absolute value,
and reduces `exp(n log q)` to `q^n`. Positivity of `q` comes from the actual
finite residue field. This is a construction identity, not an invocation of
the local functional equation.

`deligneConstant` means the unshifted epsilon constant of Deligne's convention.
It is not Deligne's distinct modified object named `epsilon_0` in section
3.4.3. `centeredConstant` is the spectral value at one half while retaining the
input Haar measure.

`SelfDualHaar` is the subtype of actual Haar measures satisfying the shared
intrinsic Fourier self-duality predicate. It has no inhabitant or existence
axiom built into its definition. The needed separation and total disconnectedness
instances are derived from the supplied valuation topology: its additive
uniformity gives separation, and equality with the valuation subgroup topology
gives the nonarchimedean ring instance. `langlandsConstantAtSelfDual` takes such a
measure explicitly and evaluates at one half. `langlandsEpsilonAtSelfDual`
takes the same input and evaluates at the spectral argument `s`. Their
half-argument identity is proved by reflexivity. These definitions retain the
distinction between Deligne's measure-dependent constant and Langlands'
half-shifted self-dual convention. Existence and uniqueness of the self-dual
measure, independence of the supplied witness, nonvanishing of the constants,
and comparison with functional equations remain separate theorem obligations.

## Original sources and exact dependencies

Tate, *Number theoretic background* (1979), sections 3.1.3 and
3.2.1--3.2.6, printed pages 12--14 (Corvallis Part II PDF pages 21--23),
supplies the rank-one L and epsilon formulas. Section 3.6.1--3.6.4,
printed page 17/PDF page 26, distinguishes the two epsilon normalizations.
The relevant formula pages were read visually. Registered source
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Deligne, *Les constantes des equations fonctionnelles des fonctions L*
(1973), sections 3.3--3.4.3, printed pages 526--528/internal PDF pages 26--28,
supplies the plus sign, fixed measure, and ramified integral. Printed page 528
was visually checked, including the distinction between epsilon and epsilon_0.
Registered source `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

The source received from Worker 33 was draft revision 5 of task
`722e8992-bab8-4859-abf9-98fa81f4cd4f`, content
`34cab37f477c26a042d6271c61f4e26afe7959c6a09b74cb5d84e8a15a2ae983`,
Lean SHA256
`ab92db7c27106fa484721ccd7328d064455b0c189e635f0bb85d03e52a15a963`
and Markdown SHA256
`dd319000ed5f360913abc88d6aac7040ca1ce3fa0fc31a06d9d53398aa9a9f09`.
Both complete files were read before adaptation. Worker 33 had checked its
original callable expressions against the earlier inlined theorem target by
reflexivity. That historical check is not a semantic review of this adapted
contribution.

The project imports are `Langlands.LocalField.Uniformizer` and
`Langlands.LocalFactor.Abelian.Definitions`; the latter imports
the actual conductor construction. Its upstream project imports and current
Library commit are recorded in the paired [Abelian/Definitions.md](Definitions.md) and
[Conductor.md](../../HarmonicAnalysis/Conductor.md). The other imports are the pinned Mathlib rational-function,
meromorphic, finite-support and integration APIs. No pending theorem proof is
assumed. Compilation does not establish independent mathematical acceptance
or current Library publication.
