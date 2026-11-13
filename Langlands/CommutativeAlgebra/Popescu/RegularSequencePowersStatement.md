# Powers of a regular sequence

`Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersStatement` (universe `u`).

**Hypotheses.**
- `R : Type u` is a commutative ring and `M : Type u` an `R`-module.
- `r : ℕ`, `f : Fin r → R` and `e : Fin r → ℕ` with `e i > 0` for all `i`.

**Conclusion.** `RingTheory.Sequence.IsRegular M (List.ofFn f)` holds if and only if
`RingTheory.Sequence.IsRegular M (List.ofFn fun i => f i ^ e i)` holds. That is,
`f₀, …, f_{r−1}` is an `M`-regular sequence exactly when `f₀^{e₀}, …, f_{r−1}^{e_{r−1}}`
is.

## Source

Stacks Project, Chapter 10 *Commutative Algebra*, version ed88ff78
(`stacks-commutative-algebra-chapter-ed88ff78`), Lemma 10.68.9 (Tag 07DV, printed
p. 162):

> Let R be a ring. Let M be an R-module. Let f₁, …, f_r ∈ R and e₁, …, e_r > 0 integers.
> Then f₁, …, f_r is an M-regular sequence if and only if f₁^{e₁}, …, f_r^{e_r} is an
> M-regular sequence.

Definition 10.68.1 (Tag 00LF, p. 161) of an `M`-regular sequence requires that each `fᵢ` is
a nonzerodivisor on `M/(f₁, …, f_{i−1})M` and that `M/(f₁, …, f_r)M ≠ 0`. This is
Mathlib's `RingTheory.Sequence.IsRegular`.

## Encoding and scope

- The finite sequences are families indexed by `Fin r`, turned into lists by `List.ofFn`.
  Indices are zero-based.
- **Use.** The proofs of Lemma 10.2 (Tag 07FD, printed p. 24) and Lemma 11.4 (Tag 07FJ,
  steps (12) and (13), printed pp. 29–30) of *Smoothing Ring Maps*
  (`stacks-artin-axioms-approximation-2026-11-06`) apply it as "π₁ᵉ, …, π_tᵉ, π_{t+1} is
  a regular sequence … by Algebra, Lemma 68.9".
- **Universe.** `R` and `M` are in one universe `u`.
