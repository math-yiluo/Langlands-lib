# End derivations of the segment polynomial ring

Module `Langlands.Representation.Aubert.SegmentEndDerivation`, namespace
`Langlands.Aubert.SegmentEndDerivation`.

This is a helper module for the polynomial side of the injectivity half of
`Langlands.Aubert.SegmentPolynomialComparisonStatement` (Zelevinsky 1980,
Corollary 7.5). Its contents are internal. Zelevinsky's own proof of 7.5 uses
the classification of irreducible representations (6.1, 6.9), not derivations.
The route here replaces his argument with a purely algebraic injectivity
criterion on the polynomial ring. That criterion is meant to be fed by
Bernstein-Zelevinsky derivatives combined with a cuspidal-support grading on
the Grothendieck side, which are built elsewhere. Nothing in this module
involves representations. Its Langlands inputs are the Library theorem
`Classification.cuspidalIntegralTwistFreeness` about cuspidal data and the existing
segment truncation in `Classification/SegmentInitialTruncation`.

Notation: for a segment `Δ = [ν^(1-m) ρ, ρ]` with end `ρ = Δ.last` and length
`m`, write `Δ⁻ = [ν^(1-m) ρ, ν^(-1) ρ]` when `m ≥ 2`. This is Zelevinsky's
`Δ⁻`: same beginning, one element fewer.

## Definitions

- The imported `Segment.dropLastNonempty Δ h`, for `h : 1 < Δ.length`, is
  the segment `⟨Δ.base, Δ.length - 1⟩`, which is `Δ⁻`. This module reuses the
  existing construction and its base and length lemmas.
- `endTail Δ`: the variable `X_{Δ⁻}` when `Δ` has length at least two, and `1`
  when `Δ` has length one.
- `endDerivation ρ`: the `ℤ`-derivation `D_ρ` of `MvPolynomial T.Segment ℤ`
  (built with `MvPolynomial.mkDerivation`) with `D_ρ X_Δ = endTail Δ` when
  `Δ.last = ρ` and `D_ρ X_Δ = 0` otherwise.
- `lengthWeight`: the additive weight `Finsupp.weight Segment.length` on
  monomials. It is the sum of the lengths of the segments in a monomial.
- `lowWeight n`: the `ℤ`-submodule of polynomials all of whose monomials have
  length weight below `n`.
- `endExpansion`: the ring homomorphism
  `MvPolynomial T.Segment ℤ →+* AddMonoidAlgebra (MvPolynomial T.Segment ℤ) (T.CuspidalDatum →₀ ℕ)`
  sending `X_Δ` to `single 0 X_Δ + single (single Δ.last 1) (endTail Δ)`, that
  is, `X_Δ + (D_{Δ.last} X_Δ) e^{Δ.last}`.
- `cuspidalMonoidInclusion`: the inclusion
  `(T.CuspidalDatum →₀ ℕ) →+ (T.CuspidalDatum →₀ ℤ)` (coefficientwise cast).

## Results

- `segment_ext`: segments with equal beginning and length are equal.
- `segment_ext_last`: segments with equal end and length are equal. Proof:
  twist the ends by `-(length - 1)` and use `twist_twist`, `twist_zero`.
- The imported `dropLastNonempty_base` and `dropLastNonempty_length` give
  the beginning and length of `Δ⁻`; `last_shorten` gives its end
  `Δ.last.twist (-1)`.
- `endDerivation_X_of_ne`, `endDerivation_X_of_eq`, `endDerivation_X`,
  `endTail_of_length_eq_one`, `endTail_of_one_lt`: the values of `D_ρ` on
  variables.
- `lengthWeight_single`, `lengthWeight_sub_single_add`, `mem_lowWeight`,
  `monomial_mem_lowWeight`, `mem_lowWeight_sup`, `eq_zero_of_mem_lowWeight_zero`:
  bookkeeping for the filtration.
- `endDerivation_mem_lowWeight`: `D_ρ` maps `lowWeight (n + 1)` into
  `lowWeight n`. Proof: expand `q` as a sum of monomials and use
  `mkDerivation_monomial`. Each term replaces one `X_Δ` by `X_{Δ⁻}` (length one
  less) or by `1`.
- `exists_twist_neg_one_notMem`: in a nonempty finite set `B` of cuspidal data,
  some `ρ ∈ B` has `ρ.twist (-1) ∉ B`. Proof: otherwise all `ρ₀.twist (-n)`
  (`n : ℕ`) lie in `B`. They are pairwise distinct by
  `Classification.cuspidalIntegralTwistFreeness` (`ρ.twist k = ρ ↔ k = 0` for
  `k : ℤ`), so `B` would be infinite.
- `notMem_vars_of_pderiv_eq_zero`: over `ℤ`, if `∂q/∂X_i = 0` then `X_i` does
  not occur in `q`. This follows from `coeff_pderiv`, since `m_i + 1 ≠ 0` in
  `ℤ`.
- `extract_eq`: let `D` and `K` be derivations, `s` a set of variables, and `L`
  an additive map that is linear over the polynomials supported on `s`. If
  `L (D X_i) = K X_i` for all `i ∈ s`, then `L ∘ D = K` on all polynomials
  supported on `s`. Proof: induction over `Algebra.adjoin`.
- `eq_C_of_endDerivation_eq_zero` (key lemma): a polynomial killed by every
  `D_ρ` is constant. Proof: suppose a variable occurs. By
  `exists_twist_neg_one_notMem` applied to the ends of the occurring segments,
  choose an occurring segment `Δ₀` with end `ρ` such that `ρ.twist (-1)` is not
  the end of any occurring segment. Then `q` is supported on the set `s` of
  segments not ending with `ρ.twist (-1)`. Every variable `X_{Δ⁻}` produced by
  `D_ρ` from a segment ending with `ρ` lies outside `s`. Extract the partial
  derivative `∂/∂X_{Δ₀}` from `D_ρ q = 0` with `extract_eq`:
  - if `Δ₀` has length one, take `L` to be the evaluation of the variables
    outside `s` at `0`. On generators in `s`, `L (D_ρ X_Δ) = ∂X_Δ/∂X_{Δ₀}`,
    because `Δ₀` is the only length-one segment ending with `ρ`, and longer ones
    map to variables outside `s`;
  - if `Δ₀` has length at least two, take `L = ∂/∂X_{Δ₀⁻}`, which is linear over
    polynomials supported on `s`. On generators in `s`,
    `L (D_ρ X_Δ) = ∂X_Δ/∂X_{Δ₀}`, because `Δ⁻ = Δ₀⁻` forces `Δ = Δ₀`.

  In both cases `∂q/∂X_{Δ₀} = L (D_ρ q) = 0`. This contradicts the occurrence of
  `X_{Δ₀}` by `notMem_vars_of_pderiv_eq_zero`.
- `injective_of_ker_stable`: a ring homomorphism `φ` from
  `MvPolynomial T.Segment ℤ` to a commutative ring `A` is injective if its
  kernel is stable under every `D_ρ` and `(c : A) = 0` forces `c = 0` for
  integers `c`. Proof: induction on `n` shows that `q ∈ lowWeight n` and
  `φ q = 0` give `q = 0`. In the step, every `D_ρ q` lies in the kernel and in
  `lowWeight n`, hence vanishes. So `q` is a constant `c`, and `φ q = c = 0`
  forces `c = 0`.
- `endExpansion_X`: the value of `endExpansion` on a variable.
- `coeff_endExpansion`: for every polynomial `q`, the coefficient of
  `endExpansion q` at `0` is `q`, and its coefficient at `single ρ 1` is
  `D_ρ q`. Proof: induction on `q` (`MvPolynomial.induction_on`). In the step
  `q * X_Δ`, write `endExpansion (q * X_Δ) = endExpansion q * (single 0 X_Δ +
  single (single Δ.last 1) (endTail Δ))`. Its coefficient at `0` is
  `(endExpansion q).coeff 0 * X_Δ`, which is `q * X_Δ` by the induction
  hypothesis: the second summand contributes nothing at `0`, because a sum of
  `ℕ`-valued finsupps involving `single Δ.last 1` is never `0`. (This is the
  degree-zero group-algebra coefficient, not the constant coefficient of the
  polynomial `q`.) The coefficient at `single ρ 1` is
  `(endExpansion q).coeff (single ρ 1) * X_Δ = (D_ρ q) X_Δ`, plus
  `(endExpansion q).coeff 0 * endTail Δ = q · endTail Δ` when `Δ.last = ρ`.
  This matches the Leibniz rule for `D_ρ (q X_Δ)`.
- `cuspidalMonoidInclusion_injective`, `cuspidalMonoidInclusion_single`.
- `injective_of_endExpansion` (injectivity criterion): let `φ` be a ring
  homomorphism from `MvPolynomial T.Segment ℤ` to a commutative ring `A` such
  that `(c : A) = 0` forces `c = 0` for integers `c`. Suppose some ring
  homomorphism `E : A →+* AddMonoidAlgebra A (T.CuspidalDatum →₀ ℤ)` satisfies
  `E (φ X_Δ) = single 0 (φ X_Δ) + single (single Δ.last 1) (φ (endTail Δ))` for
  every segment `Δ`. Then `φ` is injective. Proof: let
  `Φ = mapDomainRingHom cuspidalMonoidInclusion ∘ mapRingHom φ`. Then
  `Φ ∘ endExpansion = E ∘ φ`, since both are ring homomorphisms that agree on
  constants and variables. Because `cuspidalMonoidInclusion` is injective, the
  coefficient of `Φ y` at the image of `m` is `φ (y.coeff m)`. Hence
  `φ q = 0` gives `φ (D_ρ q) = (E (φ q)).coeff (single ρ 1) = 0`, and
  `injective_of_ker_stable` applies.

## Use

For the comparison theorem, `A` is the graded Grothendieck ring and `φ` is
`segmentPolynomialEvaluation`. The intended `E` combines the total
Bernstein-Zelevinsky derivative with a grading of the Grothendieck ring by
cuspidal support. On the class of `Z(Δ)` it returns `Z(Δ) + Z(Δ⁻) e^{Δ.last}`,
with `Z(Δ⁻) = 1` when `Δ` has length one. Those inputs are proved in separate
modules.
