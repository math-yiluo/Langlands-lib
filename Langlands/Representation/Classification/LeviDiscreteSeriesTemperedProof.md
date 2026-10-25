# Square-integrable GL block Levi representations are tempered

Author: Worker 320.

## Exact result

`Langlands.glLeviDiscreteSeriesTempered.{uF,uW}` proves exactly the published
proposition `Langlands.GLLeviDiscreteSeriesTemperedStatement.{uF,uW}` in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md).
It retains every prime `p`, every `F : PadicField.{uF} p` and supplied topological
data `T`, every positive total rank and block shape, and every representation
carrier in `Type uW`, independently of `uF`. For the actual product Levi `M`,
actual quotient `M / Z(M)`, and each Borel Haar measure `μ`, square-integrability
of an irreducible representation implies temperedness for that same measure.
The existing statement and its dependencies are unchanged.

The proof also supplies the generic theorem
`Langlands.isTemperedModCenter_of_squareIntegrable`. For any topological group,
any Borel measurable structure on its actual center quotient, and any Haar
measure on that quotient, it proves

```text
IsSquareIntegrableModCenter ρ μ → IsTemperedModCenter ρ μ.
```

The generic theorem has arbitrary independent group and representation carrier
universes. It needs no irreducibility. Both analytic predicates include
admissibility and an actual smooth unitary scalar central character; these
witnesses are retained unchanged. The source square-integrability assumption
supplies `MemLp` at exponent two for every smooth-dual functional and vector.
Its measurability component is used throughout.

## Implemented proof

The argument uses uniform right local constancy of each coefficient and left
Haar invariance. It does not construct or assume an invariant positive form,
factor the representation into tensor factors, or use an exponent criterion.

First, the private helper `bounded_of_memLp_two_right_invariant` considers a
real function `f` in `L²(G, μ)`, and a nonempty open set `S` such that
`f(q k) = f(q)` for every `q` and every `k ∈ S`. Haar positivity gives
`μ(S) > 0`. For each `q`, the indicator of the constant `f(q)` on `S` is the
indicator on `S` of the translated function `k ↦ f(q k)`. The indicator estimate
and invariance of the `L²` seminorm under left translation give

```text
‖f(q)‖ₑ · μ(S)^(1/2) ≤ eLpNorm f 2 μ.
```

Here the inequality is in the extended nonnegative reals. Write
`d = μ(S)^(1/2)` and `B = eLpNorm f 2 μ / d`. The denominator is nonzero and
the numerator is finite, so `B` is finite and the inequality implies
`‖f(q)‖ ≤ B.toReal`. No finite-measure assumption on `S` is required:
Mathlib's extended-real division lemmas apply also when `μ(S) = ∞`, in which
case the estimate forces all coefficient values to vanish. This is why no
compact open subgroup or local compactness hypothesis is needed in the generic
helper. Only left translations occur; right-invariance of Haar measure and
unimodularity are not assumed.

Second, `memLp_two_add_of_bounded` starts with a uniform bound
`‖f(x)‖ ≤ C` and `f ∈ L²`. For every `ε > 0`, it uses the pointwise inequality

```text
‖f(x)‖^(2+ε) = ‖f(x)‖² · ‖f(x)‖^ε
             ≤ C^ε · ‖f(x)‖².
```

The function on the right is integrable. The function on the left is almost
everywhere strongly measurable by the real-power measurability lemmas.
`Integrable.mono'` and `integrable_norm_rpow_iff` establish exactly
`MemLp f (ENNReal.ofReal (2 + ε)) μ`. The argument works on an arbitrary
measure space and never treats the whole Haar measure as finite.

For the representation application, fix a smooth-dual functional `ℓ` and a
vector `v`. Admissibility supplies smoothness, hence an open subgroup `K`
fixing `v`. Let `S` be its image under the actual quotient homomorphism
`G → G / Z(G)`. The quotient map is open, so `S` is open; the image of the
identity proves that it is nonempty. For the descended absolute coefficient
`f = c.coefficientNorm ℓ v`, quotient induction reduces right invariance on
`S` to

```text
ℓ(ρ(g k)v) = ℓ(ρ(g)(ρ(k)v)) = ℓ(ρ(g)v),  k ∈ K.
```

The already published central-character construction makes this coefficient
well-defined on the quotient. The first helper gives its uniform bound from
its assumed `L²` membership, and the second gives every required `L^(2+ε)`
membership. This treats every functional in the actual smooth dual directly;
there is no identification of the smooth dual with a Hilbert-space dual.
Finally the exact GL Levi theorem specializes the generic implication using
the supplied Levi topological-group instance. The irreducibility premise of
the target is retained but unused.

## Provenance and scope

The published target cites Allan J. Silberger, *Introduction to Harmonic
Analysis on Reductive p-adic Groups* (1979), Theorem 4.5.10(1)–(2), printed
pp.188–189, registered as `silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Worker 320 rehashed the retained original and read these two pages, including
rendered formulas on PDF pp.194–195, on 2026-10-25. No source-specific errata
note was present in the supplied Library notes. Silberger's first condition
is square-integrability modulo the center; his second includes temperedness
in his coefficient convention and vanishing weak constant terms.

The implemented proof is the elementary argument above, derived directly from
the Library's analytic definitions and Mathlib's Haar, indicator, and integral
comparison theorems. It does not formalize Silberger's proof, his weak constant
term assertion, or the separate comparison between his tempered-function
convention and `L^(2+ε)`. Those stronger source assertions are not needed for
this exact target. The source correspondence and alternative analytic
convention argument remain documented in the unchanged statement pair and
[TemperedInductionStatement](TemperedInductionStatement.md).

The two analytic helpers are internal lemmas grouped with this focused proof.
No parabolic induction theorem, opposite Jacquet quotient assertion, tempered
exhaustion result, or classification theorem is used or proved here.
