# Proof of uniform recurrences and compact-set growth along translation orbits

The module `Langlands.HarmonicAnalysis.FiniteTranslationOrbitProof` proves the
published statement `Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement`.
Its one public declaration is

```text
theorem Langlands.HarmonicAnalysis.finiteTranslationOrbit :
    FiniteTranslationOrbitStatement.{uG}
```

The theorem's type is exactly the Library statement, with the same arbitrary
universe `uG`. The statement module
`Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement` and its Markdown
are imported unchanged.

## What is proved

The statement Markdown gives the full meaning. In summary, take any
topological group `G : Type uG`, which need not be commutative, Hausdorff or
locally compact. Take a continuous `η : G → ℂ` whose complex span of left
translates `a ↦ η (b * a)` is finite-dimensional, and any `t : G`. Then there
are one `E : LinearRecurrence ℂ` and one real `B ≥ 1` such that

- for every `k : ℤ` and `a : G`, the sequence `n ↦ η (t ^ ((n : ℤ) + k) * a)`
  satisfies `E`; and
- for every compact `K` there is `C > 0` with
  `‖η (t ^ n * u)‖ ≤ C * B ^ n.natAbs` for all `n : ℤ` and `u ∈ K`.

`E` and `B` are fixed before `k`, `a` and `K`. Only `C` depends on `K`. The
proof uses only the two stated hypotheses on `η`. The zero function, a
zero-dimensional span, `t = 1`, the trivial group and the empty compact set
need no special treatment. In the zero-dimensional case the characteristic
polynomial is `1`, so `E` has order zero.

## Proof

The module has three private lemmas and the public theorem.

### One recurrence: `exists_orbit_recurrence`

For any `s : G`, this lemma gives one `E : LinearRecurrence ℂ` with
`E.IsSolution (fun n : ℕ => η (s ^ n * x))` for every `x : G`. It uses only
the finite-dimensionality hypothesis, not continuity.

Let `V` be the span of the left translates `fun a => η (b * a)`. Let `T` be
`LinearMap.funLeft ℂ ℂ (fun a => s * a)` on `G → ℂ`, so that
`T f = fun a => f (s * a)`. `T` sends the generator for `b` to the generator
for `b * s`, because `η (b * (s * a)) = η ((b * s) * a)`. Hence
`V ≤ V.comap T`, by `Submodule.span_le`. This uses associativity only, so no
commutativity of `G` is needed. Let `Tv : Module.End ℂ V` be the restriction
`T.restrict`. Induction on `m`, using `pow_succ` and `pow_succ'`, gives
`((Tv ^ m) w : G → ℂ) x = (w : G → ℂ) (s ^ m * x)` for all `w ∈ V` and `x`.

The vector `w = η` lies in `V`, as the translate by `b = 1`. Let `p` be
`Tv.charpoly`. It exists because `V` is finite-dimensional, and it is monic.
By Cayley–Hamilton (`LinearMap.aeval_self_charpoly`), `aeval Tv p = 0`.
Expanding with `Polynomial.aeval_eq_sum_range` and using monicity gives

```text
∑ i ∈ Finset.range d, p.coeff i • Tv ^ i + Tv ^ d = 0,   d = p.natDegree.
```

Apply this endomorphism to `(Tv ^ n) w` and evaluate at `x`. With the power
formula and `pow_add`, the result is

```text
∑ i < d, p.coeff i * η (s ^ (n + i) * x) + η (s ^ (n + d) * x) = 0.
```

So `E = ⟨d, fun i => -p.coeff i⟩` works for every `x`. `E` depends only on
`η` and `s`.

### Recurrence growth: `norm_le_of_isSolution`

Let `u : ℕ → ℂ` satisfy `E`. Suppose `1 ≤ B`, `∑ i, ‖E.coeffs i‖ ≤ B` and
`0 ≤ C`, and suppose `‖u i‖ ≤ C` for every `i < E.order`. Then
`‖u n‖ ≤ C * B ^ n` for all `n : ℕ`.

The proof is by strong induction on `n`. If `n < E.order`, use the initial
bound and `1 ≤ B ^ n`. Otherwise write `n = m + E.order`. The recurrence and
the triangle inequality bound `‖u n‖` by
`∑ i, ‖E.coeffs i‖ * (C * B ^ (m + i))`. Since `m + i + 1 ≤ m + E.order`,
each term satisfies `B * (C * B ^ (m + i)) ≤ C * B ^ (m + E.order)`. Then `B`
times the sum is at most `(∑ i, ‖E.coeffs i‖) * (C * B ^ n)`, which is at
most `B * (C * B ^ n)`. Cancelling `B > 0` gives the claim. For order zero
the sum is empty and `u n = 0`.

### Initial values on a compact set: `exists_orbit_initial_bound`

For `s : G`, `D : ℕ` and compact `K`, there is `C ≥ 0` with
`‖η (s ^ i * u)‖ ≤ C` for all `i < D` and `u ∈ K`. The set
`⋃ i ∈ Finset.range D, (fun u => s ^ i * u) '' K` is a finite union of
continuous images of `K`, so it is compact (`Finset.isCompact_biUnion`). The
continuous `η` is bounded on it (`IsCompact.exists_bound_of_continuousOn`).
Taking `max C 0` makes the bound nonnegative, which matters when `K` is
empty.

### Assembly: `finiteTranslationOrbit`

Apply `exists_orbit_recurrence` to `t`, giving `E₁`, and to `t⁻¹`, giving
`E₂`. The theorem's recurrence is `E := E₁`, and

```text
B := max 1 (max (∑ i, ‖E₁.coeffs i‖) (∑ i, ‖E₂.coeffs i‖)).
```

Both are fixed before any shift, point or compact set.

- **Recurrence.** By `zpow_add`, `zpow_natCast` and associativity,
  `η (t ^ ((n : ℤ) + k) * a) = η (t ^ n * (t ^ k * a))`. This is the orbit
  sequence of `E₁` at `x = t ^ k * a`.
- **Growth.** Given compact `K`, take `C₁` from the initial-bound lemma for
  `t` and `D = E₁.order`, and `C₂` for `t⁻¹` and `D = E₂.order`. Put
  `C := max C₁ C₂ + 1 > 0`. Every integer is `m` or `-m` for some `m : ℕ`
  (`Int.eq_nat_or_neg`). For `n = m`, `t ^ n = t ^ m` and `n.natAbs = m`;
  the growth lemma for `E₁` at `x = u` gives `‖η (t ^ m * u)‖ ≤ C * B ^ m`.
  For `n = -m`, `t ^ n = (t⁻¹) ^ m` (`zpow_neg`, `inv_pow`) and
  `n.natAbs = m`; the growth lemma for `E₂` gives the same bound. Both cases
  use `B ≥ 1` and the coefficient sums bounded by `B`.

The second recurrence `E₂` is used only for the growth estimate. It is not
the `E` of the conclusion.

The check `lean_check` reported 0 errors and 0 warnings for this module. The
inspection reported `finiteTranslationOrbit` as a theorem with level parameter
`uG` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the literature

The statement is a derived internal interface, not a numbered theorem of the
sources. Its Markdown explains the derivation. The hypotheses follow the
definition of finite functions in H. Jacquet, I. I. Piatetski-Shapiro and
J. Shalika, *Automorphic forms on GL(3) I*, Ann. of Math. (2) **109** (1979),
§(2.2), printed p. 181 (registered source `jps-1979-gl3-i`, one-based PDF
p. 14). That page defines a finite function on a locally compact abelian
group as "a continuous function whose translates span a finite dimensional
vector space". The proof re-read this passage on 2026-10-28. The statement
generalizes it to arbitrary topological groups with left translates. The
intended use is the valuation-shell analysis of one-variable integrals in
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), proof of Theorem (2.7), printed
pp. 391–392, display (6) (registered source `jpss-1983-rankin-selberg`).

Neither source proves this statement in this form. The proof above is the
implemented Lean argument. It is standard finite-dimensional linear algebra
(Cayley–Hamilton) together with an elementary recurrence estimate. It follows
the route the statement Markdown suggests for the recurrence. For growth it
does not use a norm on `V` or bounds on operator powers. Instead it applies
the recurrence estimate to `t` and `t⁻¹` separately.

The proof does not decompose `η` into characters or character polynomials.
It does not establish Mellin convergence, rational continuation or
denominator statements. These remain obligations of the parent one-variable
Mellin proof.

## Attribution

Worker 277 wrote this module. It reuses no other worker's draft or Library
proof code. It imports only the statement module and Mathlib
(`Mathlib.LinearAlgebra.Charpoly.Basic` and
`Mathlib.Topology.Algebra.Group.Basic`).
