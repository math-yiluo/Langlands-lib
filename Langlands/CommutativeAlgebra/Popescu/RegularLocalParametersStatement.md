# A minimal generating set of the maximal ideal of a regular local ring is regular

`Langlands.CommutativeAlgebra.Popescu.RegularLocalParametersStatement` (universe `u`).

**Hypotheses.**
- `R : Type u` is a regular local ring (`IsRegularLocalRing R`).
- `x : Fin d → R`, where `d = (IsLocalRing.maximalIdeal R).spanFinrank` is the least number
  of generators of the maximal ideal `𝔪`.
- `Ideal.span (Set.range x) = 𝔪`.

**Conclusion.** `RingTheory.Sequence.IsRegular R (List.ofFn x)`: the sequence
`x₀, …, x_{d−1}` is an `R`-regular sequence. In Mathlib this means that each `xᵢ` is a
nonzerodivisor on `R/(x₀, …, x_{i−1})` and that `R ≠ (x₀, …, x_{d−1})R`.

## Source

Stacks Project, Chapter 10 *Commutative Algebra*, version ed88ff78
(`stacks-commutative-algebra-chapter-ed88ff78`), Lemma 10.106.3 (Tag 00NQ, printed
p. 253):

> Let R be a regular local ring and let x₁, …, x_d be a minimal set of generators for the
> maximal ideal m. Then x₁, …, x_d is a regular sequence, and each R/(x₁, …, x_c) is a
> regular local ring of dimension d − c. In particular R is Cohen-Macaulay.

Definition 10.68.1 (Tag 00LF, p. 160) of an `M`-regular sequence `f₁, …, f_r`: "(1) fᵢ is a
nonzerodivisor on M/(f₁, …, f_{i−1})M for each i = 1, …, r, and (2) the module
M/(f₁, …, f_r)M is not zero." This is Mathlib's `RingTheory.Sequence.IsRegular`.

## Encoding and scope

- **Minimal generating set.** A minimal set of generators of `𝔪` is encoded as a family
  indexed by `Fin d` with `d` the least number of generators of `𝔪` (Mathlib's
  `Submodule.spanFinrank`), generating `𝔪`. By Nakayama's lemma, every generating family
  of this length is minimal, and every minimal generating set has this length.
- **Scope.** Only the first assertion of the source lemma ("x₁, …, x_d is a regular
  sequence") is stated. The assertions about `R/(x₁, …, x_c)` and Cohen–Macaulayness are
  not.
- **Use.** The proof of Lemma 11.4 of *Smoothing Ring Maps* (Tag 07FJ, steps (10), (12)
  and (13), printed pp. 28–30) applies this lemma to `k[y₁, …, y_m]_p` and to `Λ_q`. The
  proof of Lemma 10.2 (Tag 07FD) applies it to `Λ_q`.
- **Universe.** `R` is in universe `u`.
