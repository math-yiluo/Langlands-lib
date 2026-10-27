# Uniform recurrences and compact-set growth along translation orbits

`Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement.{uG}` is a
Prop-valued definition. The module states a finite-dimensional fact about
translation orbits of finite functions and supplies no proof. It is a
derived internal interface for the valuation-shell recurrence route to the
one-variable Mellin target `Langlands.RankinSelberg.OneVariableMellinStatement`.
It is not a separately numbered result of the cited literature. It does not
assert any Mellin convergence, rational continuation or denominator
statement.

## Exact scope

The proposition quantifies over

- every `G : Type uG` with instances `Group G`, `TopologicalSpace G` and
  `IsTopologicalGroup G`; the universe `uG` is arbitrary;
- every function `η : G → ℂ` that is `Continuous` and whose complex span of
  left translates is finite-dimensional:

  ```text
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun b : G => fun a : G => η (b * a))));
  ```

- every element `t : G`.

These are the only hypotheses. The group need not be commutative, locally
compact or Hausdorff. No recurrence, growth bound, character or
character-polynomial decomposition, topology on the function span, or
selected norm is supplied as an input.

The conclusion is

```text
∃ (E : LinearRecurrence ℂ) (B : ℝ), 1 ≤ B ∧
  (∀ (k : ℤ) (a : G), E.IsSolution (fun n : ℕ => η (t ^ ((n : ℤ) + k) * a))) ∧
  ∀ K : Set G, IsCompact K → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℤ, ∀ u ∈ K, ‖η (t ^ n * u)‖ ≤ C * B ^ n.natAbs.
```

Here `t ^ m` for `m : ℤ` is the group's integer power. `‖·‖` is the complex
absolute value, and `B ^ n.natAbs` is a natural-number power of the real
number `B`.

- **Recurrence.** `LinearRecurrence ℂ` and `LinearRecurrence.IsSolution`
  are Mathlib's unchanged definitions (`Mathlib.Algebra.LinearRecurrence`).
  For `E = ⟨d, c⟩`, `E.IsSolution u` means
  `∀ n : ℕ, u (n + d) = ∑ i : Fin d, c i * u (n + i)`. Thus every sequence
  `n ↦ η (t ^ (n + k) * a)` satisfies
  `η (t ^ (n + d + k) * a) = ∑ i, c i * η (t ^ (n + i + k) * a)` for all
  `n : ℕ`. Because the integer shift `k` is arbitrary, the recurrence holds
  along the whole two-sided orbit `m ↦ η (t ^ m * a)`, `m : ℤ`.
- **Growth.** For every compact `K` there is a positive constant `C` with
  `‖η (t ^ n * u)‖ ≤ C * B ^ |n|` for all integers `n`, both positive and
  negative, and all `u ∈ K`.
- **Uniformity.** The quantifier order is part of the statement. `E` and
  `B` are chosen once for the given `η` and `t`, before the shift `k`, the
  base point `a` and the compact set `K`. Only `C` may depend on `K`. Both
  `E` and `B` may depend on `G`, `η` and `t`.

Edge cases are included rather than excluded. These include the zero
function, whose translation span is zero-dimensional, as well as `t = 1`,
the trivial group and the empty compact set. Order-zero recurrences are
permitted. For order zero the condition says that each orbit sequence
vanishes identically, with the empty sum equal to `0`.

The proposition is the only new public declaration. It uses only Mathlib
names, and no auxiliary operator, orbit space, basis or coordinate system
appears in it. Existing Library pairs are unchanged.

## Original sources and derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic forms on GL(3) I*, Annals of Mathematics (2) **109**
  (1979), 169–212, §(2.2), printed p. 181 (one-based PDF p. 14). That page
  defines a finite function on a locally compact abelian group as a
  continuous function whose translates span a finite-dimensional vector
  space. Registered source `jps-1979-gl3-i`, file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, proof of Theorem (2.7), printed pp. 391–392 (one-based
  PDF pp. 26–27), especially display (6) on p. 392 and the paragraphs that
  follow it. Registered source `jpss-1983-rankin-selberg`, file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Both passages were read in the retained files on 2026-10-27. The JPSS scan
has no text layer, so pp. 391–392 were rendered and read visually. Neither
the project nor the Library at base commit `2ae54bcc` had an errata note
for these sources.

**Hypotheses.** The hypotheses on `η` follow the 1979 definition: continuity
plus a finite-dimensional translation span. The definition is generalized
from locally compact abelian groups to arbitrary topological groups. The
Lean convention uses left translates `a ↦ η (b * a)`. On an abelian group
these are exactly the translates of the source, which is the case of the
multiplicative group `F^×` of a local field used downstream.

**Derivation.** On p. 392, JPSS reduce the integrals to products of
one-variable integrals `∫ Φ_i(a_i) η_i(a_i) |a_i|^{is} d^×a_i` (display
(6)), with `Φ_i` Schwartz functions and `η_i` finite functions on `F^×`.
They then state that these converge for large real part. They also state
that, with `X = q^{-s}`, each integral has the form `Q_i(X) (1 - α_i X)^{-k_i}`,
with `α_i` depending only on `η_i`. On a nonarchimedean field, write
`a = ϖ^n u` with a uniformizer `ϖ` and `u` in the compact unit group. The
integral then becomes a sum over valuation shells indexed by `n`. Taking
`G = F^×` and `t = ϖ`, the recurrence conclusion makes the shell values of
`η` satisfy one linear recurrence. That recurrence is independent of the
shell coordinate `u` and of shifts in `n`, which is the source of a
denominator determined by `η` alone. The growth conclusion, uniform over
the compact unit group, gives the absolute-convergence bound for large
real part. This explains the derived formulation. The statement itself
records only the finite-dimensional orbit facts. Using it for
convergence, continuation or denominators remains the parent proof's
obligation.

## Remaining proof obligation

A later exact-target proof task must prove this proposition from the
stated hypotheses alone. One possible route is the following, which is a
suggestion and not something assumed or implemented here. Let `V` be the
finite-dimensional translation span. Left multiplication by `t` in the
argument, `f ↦ (a ↦ f (t * a))`, preserves `V` and is invertible on it.
Its characteristic polynomial, by Cayley–Hamilton, then gives a
recurrence that is uniform in evaluation points and shifts. Finitely many
evaluation points separating `V` give a norm on `V`. Powers of the
operator and its inverse are exponentially bounded, and continuity of the
basis functions bounds the coordinates on compact sets. Compilation
checks only that the declaration is a well-formed proposition
(`statement_returns_prop`). It does not establish the mathematical
theorem.

Worker 277 authored this pair from the task contract's formulation, which
was requested for Worker 656's one-variable Mellin proof route.
