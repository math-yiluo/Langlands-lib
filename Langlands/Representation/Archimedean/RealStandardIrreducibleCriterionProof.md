# Proof: Speh's irreducibility criterion for `GL_n(ℝ)`, "if" direction

Module `Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionProof`. The theorem

```lean
theorem Langlands.Archimedean.realStandardIrreducibleCriterion :
    RealStandardIrreducibleCriterionStatement
```

proves `Langlands.Archimedean.RealStandardIrreducibleCriterionStatement` (module
`RealLargeStandardIrreducibleReduction`; the statement has no universe parameter). Unfolded, the
statement is

```lean
∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
  IsRealMoeglinUnlinked ds →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)
```

In words: for a list `ds` of real blocks of total rank `n` in Langlands order, if no two Mœglin
data of the blocks are linked (`IsRealMoeglinUnlinked`, the condition of Mœglin's Theorem 10b),
then the `(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite functions of the standard module of `ds` is
irreducible.

## Proof as implemented

The proof is a single term of Library theorems.

1. `realStandardIrreducibleCriterionReduction` (module `RealStandardIrreducibleCriterionReduction`)
   proves `RealStandardIrreducibleCriterionReductionStatement`:
   `RealStandardLanglandsQuotientStatement → RealUnlinkedSwapStatement →
   RealReverseIntertwinerKernelStatement → RealStandardIrreducibleCriterionStatement`.
   Composing unlinked swaps gives an injective intertwiner from the standard module of `ds` to
   that of `ds.reverse`; its kernel contains every proper `(𝔤, K)`-submodule, so the only proper
   submodule is zero.
2. `RealStandardLanglandsQuotientStatement` (every Langlands-ordered standard module has a
   largest proper `(𝔤, K)`-submodule) is the term
   `realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration
   realTemperedStandardIrreducible`. Here `realLeviLanglandsQuotient` (module
   `RealLeviLanglandsQuotient`) proves `RealLeviLanglandsQuotientStatement`, the implication
   `RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
   RealTemperedStandardIrreducibleStatement → RealStandardLanglandsQuotientStatement`.
3. `RealUnlinkedSwapStatement` (exchanging two adjacent unlinked blocks, the first with the
   larger or equal exponent, gives an injective intertwiner) is the Library theorem
   `realUnlinkedSwap` (module `RealLinkedLanglandsQuotientNotLargeProof`).
4. `RealReverseIntertwinerKernelStatement` (every intertwiner from a Langlands-ordered standard
   module to the standard module of the reversed list vanishes on every proper
   `(𝔤, K)`-submodule) is the term `realReverseIntertwinerKernelReduction realLeviChartIntegrable
   realLeviParabolicIntegration realTemperedStandardIrreducible`. Here
   `realReverseIntertwinerKernelReduction` (module `RealReverseIntertwinerKernel`) proves
   `RealReverseIntertwinerKernelReductionStatement`, with the same three premises as in step 2.
5. The three premises are Library theorems: `realLeviChartIntegrable` (module
   `RealLeviChartIntegrable`, integrability of the Gram bound on the opposite unipotent radical),
   `realLeviParabolicIntegration` (module `RealLeviParabolicIntegration`, integration over
   `O(N)` in coordinates of a standard parabolic subgroup) and `realTemperedStandardIrreducible`
   (module `RealTemperedIrreducibleProof`, irreducibility of tempered real standard modules).

The same subterm `realStandardIrreducibleCriterionReduction hL realUnlinkedSwap hRev` occurs in
the Library's proof of `realLargeLanglandsQuotientInjective` (module
`RealLargeLanglandsQuotientInjectiveProof`), where the tempered premise is assembled locally;
here it is the theorem `realTemperedStandardIrreducible`.

## Declarations

- `realStandardIrreducibleCriterion : RealStandardIrreducibleCriterionStatement` (theorem).

## Provenance

C. Mœglin, *Representations of GL(n) over the real field*, in T. N. Bailey and A. W. Knapp
(eds.), *Representation Theory and Automorphic Forms*, Proc. Sympos. Pure Math. 61 (1997),
157–166, registered as `bailey-knapp-1997-pspm61` (the proceedings volume; printed p. 164 is PDF
page 173 of the volume).

- §10, Theorem 10b, printed p. 164: "If `χ` is as above, then `I(χ)` is irreducible if and only
  if for all `i, j ∈ [1, t]` with `n_i ≥ n_j`, either `s_i − s_j ∉ ℝ` or the appropriate one of
  the following conditions holds", conditions (i)–(iii) for pairs of characters, a character and
  a discrete series, and two discrete series. Mœglin attributes the theorem to Speh's thesis
  ([Sp1]). The theorem here is the "if" direction for Langlands-ordered lists of the Library's
  real blocks; `IsRealMoeglinUnlinked` says that no pair of data satisfies the linking relation
  that the conditions exclude.
- §8, "Proof of Theorem 1", printed p. 163: the normalized intertwining operators `A'(w, χ_s)`
  are holomorphic and bijective under the irreducibility conditions, giving an isomorphism
  between `I(χ_{s₀})` and `I(w₀χ_{s₀})`, and the Langlands theorem then identifies it with the
  irreducible `J(χ_{s₀})`. The reduction above follows this argument: the unlinked swaps play
  the role of the bijective rank-one operators, and the kernel statement that of the Langlands
  theorem.
