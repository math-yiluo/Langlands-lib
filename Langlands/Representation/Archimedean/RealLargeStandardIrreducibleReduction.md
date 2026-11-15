# Splitting Vogan's irreducibility statement for `GL_n(ℝ)` along Speh's criterion

Lean module: `Langlands.Representation.Archimedean.RealLargeStandardIrreducibleReduction`.

This module splits `Langlands.Archimedean.RealLargeStandardIrreducibleStatement` (statement V
of `RealLargeLanglandsQuotientReduction.md`) into two statements. It proves the implication
`realLargeStandardIrreducibleReduction` (the two statements imply V). No hypothesis is added
to V. The two statements are only stated here and still need proofs.

Notation as in `RealLargeLanglandsQuotientReduction.md`: for a list `ds` of real blocks,
`I(ds)` is the `(𝔤𝔩_n(ℝ), O(n))`-module `(realStandardRep n ds, realStandardLie n ds)` on the
`O(n)`-finite functions of `realStandardModule n ds`. `IsGKSubmodule` and
`IsMaximallyFaithfulModulo` are the definitions of that module.

## Mœglin's data

Mœglin 1997, §10 (printed p. 164), writes a standard module of `GL(n, ℝ)` as `I(χ)`, where
`χ = {(n_j, s_j, σ_j)}_{j ∈ [1, t]}` with `n_j ∈ {1, 2}` and `s_j ∈ ℂ`:

* if `n_j = 1`, `σ_j` is a character of `ℝ^×` of order at most 2 (`1` or `sgn`);
* if `n_j = 2`, there is an integer `p_j ≥ 1`, and `σ_j` is the unique discrete series of
  `GL(2, ℝ)` with infinitesimal character `(p_j/2, -p_j/2)`.

`I(χ)` is the `(𝔤, O(n))`-module induced from `⊗_j σ_j ⊗ |det_{GL(n_j)}|^{s_j}` via the
parabolic subgroup containing the upper triangular Borel subgroup `B`. Mœglin calls `χ`
positive when `Re s_i ≥ Re s_j` for all `i < j`. This is the Library's
`IsRealLanglandsOrdered`.

Definitions in Lean:

* `MoeglinDatum`: `character ε s` is the datum `(1, s, sgn^ε)`, with `ε : Fin 2`;
  `discrete p s` is the datum `(2, s, σ)`, with `σ` the discrete series of infinitesimal
  character `(p/2, -p/2)`. The type itself does not require `p ≥ 1`. The data produced by
  `realBlockMoeglinData` satisfy it.
* `MoeglinDatum.IsLinked a b`: the pair `a`, `b` violates the condition of Mœglin's
  Theorem 10b. By cases:
  * two characters `(1, s, sgn^ε)`, `(1, s', sgn^ε')`: there is an integer `k ≠ 0` with
    `s - s' = k` and `k + ε + ε'` odd. So `k` is odd if `ε = ε'` and even if `ε ≠ ε'`.
    This is the negation of 10b(i): "`|s_i - s_j|` is not an even (resp. odd) nonzero
    integer if `σ_i ≠ σ_j` (resp. `σ_i = σ_j`)", together with `s_i - s_j ∈ ℝ`;
  * a discrete series datum `(2, s, D_p)` and a character `(1, s', σ')`, in either order:
    there is a natural number `k > 0` with `s - s' = p/2 + k` or `s' - s = p/2 + k`. That
    is, `s - s'` is real and `|s - s'| - p/2 ∈ {1, 2, 3, …}`, the negation of 10b(ii);
  * two discrete series data `(2, s, D_p)`, `(2, s', D_p')`: there is `k > 0` with
    `s - s' = |p - p'|/2 + k` or `s' - s = |p - p'|/2 + k`. In Lean `|p - p'|` is
    `((p : ℤ) - p').natAbs`. This is the negation of 10b(iii):
    `-|p_i - p_j|/2 + |s_i - s_j| ∉ {1, 2, 3, …}`.

  The relation is symmetric. Mœglin quantifies over pairs `i, j` with `n_i ≥ n_j`, and the
  case split above covers both orders of a mixed pair. For `i = j` her conditions always
  hold (`s_i - s_j = 0`), so only pairs of distinct data matter.
* `realBlockMoeglinData`: the Mœglin data of one real block.
  * `RealBlock.character d` is the character `sgn^ε |·|^t` with `ε = d.parity` and
    `t = d.exponent` (`RealCharacterData.character_eq`). It gives `[character ε t]`.
  * `RealBlock.induced d` of weight `m = d.weight ≠ 0` and exponent `t = d.exponent` is the
    block `D_|m| ⊗ |det|^t` of `GL_2(ℝ)`: the subrepresentation of
    `Ind(sgn^(|m|+1) |·|^(t+|m|/2) ⊗ |·|^(t-|m|/2))` cut out by the Fourier condition, with
    lowest `SO(2)`-weight `|m| + 1` and infinitesimal character `(t + |m|/2, t - |m|/2)`
    (`StandardModule.md`, item 2 of its comparison with Knapp). This is
    `σ ⊗ |det|^t` with `σ` Mœglin's discrete series for `p = |m|`. It gives
    `[discrete |m| t]`.
  * `RealBlock.induced d` of weight `0` is the full principal series
    `Ind(sgn |·|^t ⊗ |·|^t)`, because the Fourier condition is vacuous
    (`StandardModule.md`, item 3). Induction in stages makes it the part of `I(χ)` given by
    the two data `(1, t, sgn)` and `(1, t, 1)`. It gives `[character 1 t, character 0 t]`.

  So the standard module of `ds` is Mœglin's `I(χ)` for `χ = realMoeglinData ds`. The two
  data of a weight-`0` block have the same `s`, so Mœglin positivity of `χ` is
  `IsRealLanglandsOrdered ds`.
* `realMoeglinData ds`: the concatenation of the data of the blocks, in order
  (`List.flatMap`).
* `IsRealMoeglinUnlinked ds`: `(realMoeglinData ds).Pairwise fun a b => ¬ a.IsLinked b`.
  No two distinct entries of the list are linked. By symmetry this is exactly the
  condition of Theorem 10b for all pairs `i, j`.

A note on a sign in the source. Mœglin also writes `σ_j` as "the unique irreducible
submodule of `I(ε|·|^{p_j/2} × |·|^{-p_j/2})`, where `ε` is the sign character if `p_j` is
odd and is the trivial character otherwise". The sign there is reversed. For `p_j = 1` the
discrete series with infinitesimal character `(1/2, -1/2)` has even `SO(2)`-weights, so it
lies in the principal series `|·|^{1/2} × |·|^{-1/2}` with no sign. Badulescu–Renard
2010, (9.1), state the reducibility condition for `δ(α_1, ε_1) × δ(α_2, ε_2)` as
`α_1 - α_2 = p ∈ ℤ ∖ {0}` and `ε_1 - ε_2 ≡ p + 1 (mod 2)`. The Library's sign
`sgn^(|m|+1)` on the first character agrees with this. Theorem 10b is stated in terms of
`p_j` and `s_j` only,
so the definitions above follow the primary description of `σ_j` by its infinitesimal
character.

## The two statements

1. `RealStandardIrreducibleCriterionStatement` (Sp). Let `ds` be a list of real blocks with
   `realRank ds = n`, `IsRealLanglandsOrdered ds` and `IsRealMoeglinUnlinked ds`. Then
   `IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)`: `I(ds)` is nonzero
   and has no `(𝔤, K)`-submodules other than `0` and itself.

   Source: Mœglin 1997, Theorem 10b (printed p. 164), the "if" direction. Mœglin attributes
   the theorem to Speh's thesis ([Sp1]). The theorem holds for every `χ`. Sp keeps only the
   Langlands-ordered case, which is all the reduction needs, so Sp is weaker than the
   source.

2. `RealLinkedLanglandsQuotientNotLargeStatement` (NL). Let `ds` be a list of real blocks
   with `realRank ds = n` and `IsRealLanglandsOrdered ds`, and suppose
   `¬ IsRealMoeglinUnlinked ds`, so two Mœglin data of the blocks are linked. Let `R` be a
   largest proper `(𝔤, K)`-submodule of `I(ds)`, with the same three properties as in V.
   Then `¬ IsMaximallyFaithfulModulo (realStandardLie n ds) R`: the Langlands quotient
   `I(ds) / R` is not maximally faithful.

   Why NL is true. By the "only if" direction of Theorem 10b, `I(ds)` is reducible. Vogan
   1978, Theorem 6.2 (p. 89), (a) ⇒ (f), with its proof (p. 93), says that the standard
   module of a large irreducible Langlands quotient is irreducible.
   `RealLargeLanglandsQuotientReduction.md` explains why maximal faithfulness of the
   irreducible quotient `I(ds) / R` is Vogan's "large". So `I(ds) / R` is not maximally
   faithful. NL is thus Vogan's theorem restricted to reducible standard modules, with
   reducibility detected by Speh's criterion. A proof of NL needs a route that does not
   go through V itself. One possible route uses Gelfand–Kirillov dimension: Vogan 1978,
   Lemma 6.5 and Corollary 6.6 (p. 94), together with the composition series of the
   reducible induced modules of `GL_2`, `GL_3` and `GL_4` that come from a single linked
   pair.

As with V, proofs of Sp and NL must identify the Library's `realStandardModule n ds` and its
`O(n)`-finite part with Mœglin's `I(χ)`, as described above.

## The reduction

`RealLargeStandardIrreducibleReductionStatement` is the implication Sp → NL → V. The
theorem `realLargeStandardIrreducibleReduction` proves it. It assumes the hypotheses of V for
`n`, `ds` and `R`, including `IsMaximallyFaithfulModulo (realStandardLie n ds) R`, and splits
on `IsRealMoeglinUnlinked ds`:

* If it holds, Sp makes `I(ds)` irreducible. `R` is stable under `realStandardRep` and
  `realStandardLie` (the two halves of `IsGKSubmodule`), so `R = ⊥` or `R = ⊤`. Since
  `R ≠ ⊤`, `R = ⊥`.
* If it fails, NL says that `R` is not maximally faithful, which contradicts the hypothesis.

The proof uses neither the maximality of `R` nor the ordering, beyond passing them to Sp
and NL.

## Provenance

Derived. `MoeglinDatum`, `MoeglinDatum.IsLinked` and `IsRealMoeglinUnlinked` transcribe the
data and conditions of Mœglin 1997, §10 and Theorem 10b. `realBlockMoeglinData` translates
the Library's blocks into her data, as justified above using `StandardModule.md`. Sp is the
"if" direction of Theorem 10b (Speh), restricted to Langlands-ordered lists. NL combines the
"only if" direction of Theorem 10b with Vogan 1978, Theorem 6.2, (a) ⇒ (f). The split into
Sp and NL and the proof of the implication are internal to this module.

Sources:

* C. Mœglin, Representations of GL(n) over the real field, in: T. N. Bailey and
  A. W. Knapp (eds.), Representation Theory and Automorphic Forms, Proc. Sympos. Pure
  Math. 61 (1997), 157–166 (`bailey-knapp-1997-pspm61`). §10, the data `χ` and positivity,
  Theorem 10a and Theorem 10b, printed p. 164 (PDF page 173 of the proceedings volume).
* D. A. Vogan, Gelfand–Kirillov dimension for Harish-Chandra modules, Invent. Math. 48
  (1978), 75–98. Definition 6.1 and Theorem 6.2 (p. 89), proof of (a) ⇒ (f) (p. 93),
  Lemma 6.5 and Corollary 6.6 (p. 94). In the registered folder
  `provided-7fc98c3cf1cf4a28ee355a474ea2850645ab4bb5a37e25028414c938744c0cdf`; PDF page =
  printed page − 74.
* A. I. Badulescu and D. Renard, Unitary dual of GL(n) at archimedean places and global
  Jacquet–Langlands correspondence, Compositio Math. 146 (2010), 1115–1164
  (`badulescu-renard-2010-unitary-dual`), §9.2, (9.1) (printed p. 1133, PDF page 20):
  the reducibility condition for principal series of `GL(2, ℝ)`, which fixes the sign of
  the principal series containing the discrete series.
