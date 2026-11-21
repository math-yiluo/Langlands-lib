# Injectivity of maps onto large Langlands quotients of `GL_n(ℝ)`

`Langlands.Archimedean.realLargeLanglandsQuotientInjective` has type
`Langlands.Archimedean.RealLargeLanglandsQuotientInjectiveStatement.{uV}` from
[`RealGenericLargeReduction`](RealGenericLargeReduction.md). It adds no hypotheses.
For a list `ds` of rank `n` in Langlands order, write `I(ds)` for the actual
`O(n)`-finite functions in `realStandardModule n ds`, with actions
`realStandardRep n ds` and `realStandardLie n ds`. A nonzero complex-linear
intertwiner `B` from `I(ds)` into an irreducible admissible real `(𝔤, K)`-module
with maximally faithful Lie action is injective. The target retains the
compatibility and admissibility hypotheses as well as the arbitrary universe `uV`.

## Proof in Lean

1. **Irreducibility within ties.** The local proof `hScal` uses
   `realTemperedScalarCommutant_of_cases` on lists whose block exponents have
   the same real part. Without a nonzero-weight induction block,
   `realTiedNondiscreteReduction RealSphericalCyclicProof.realSphericalCyclic`
   supplies scalarity, including the empty list. With such a block,
   `realTiedDiscreteScalarCommutant_of_cases` splits on
   `IsRealDiscreteExponentSeparated ds`: a block at the same complex exponent
   as a discrete-series block must have the same absolute weight for separation
   to hold. The two inputs are
   [`realTiedDiscreteSeparatedScalarCommutant`](RealDiscreteSeparatedProof.md)
   and [`realTiedDiscreteCoincidentScalarCommutant`](RealDiscreteCoincidentProof.md).
   These cases prove that every endomorphism commuting with both actions on
   `I(ds)` is scalar. The form theorem [`realTemperedForm`](RealTemperedFormProof.md)
   and `hScal` supply `hTemp` by
   [`realTemperedStandardIrreducible_of_form_of_scalarCommutant`](RealTemperedCommutantReduction.md).
   The invariant complements furnished by the form give equivariant projections;
   a scalar projection is zero or the identity.
2. **The quotient and reverse kernels.** The proved chart integrability and
   parabolic integration formula (`realLeviChartIntegrable`,
   `realLeviParabolicIntegration`), with `hTemp`, are inputs to both analytic
   reductions. [`realLeviLanglandsQuotient`](RealLeviLanglandsQuotient.md) gives
   `hL : RealStandardLanglandsQuotientStatement`: there is a largest proper
   `(𝔤, K)`-submodule `R` of `I(ds)`. In that proof the Levi limit yields a nonzero
   linear functional killing every proper stable subspace; their supremum is
   therefore proper. [`realReverseIntertwinerKernelReduction`](RealReverseIntertwinerKernel.md)
   gives `hRev`: any intertwiner `I(ds) → I(ds.reverse)` kills every proper
   `(𝔤, K)`-submodule of `I(ds)`. Both arguments use the parabolic whose blocks
   are the tie classes, so the order does not have to be strict within a class.
3. **A large quotient forces `R = ⊥`.**
   [`realLargeStandardIrreducibleReduction`](RealLargeStandardIrreducibleReduction.md)
   splits on `IsRealMoeglinUnlinked ds`. In the unlinked case,
   [`realStandardIrreducibleCriterionReduction`](RealStandardIrreducibleCriterionReduction.md)
   composes injective adjacent swaps from `realUnlinkedSwap` into an injective
   reverse intertwiner. The reverse-kernel theorem forces every proper stable
   subspace to be zero; `hL` also ensures the source is nonzero. In the linked
   case, [`realLinkedLanglandsQuotientNotLarge`](RealLinkedLanglandsQuotientNotLargeProof.md)
   rules out maximal faithfulness modulo `R`: the linked Jacquet functional
   gives an upper bound on quotient growth that contradicts the central-ideal
   lower bound under maximal faithfulness.
4. **Apply this to the given map.**
   [`realLargeLanglandsQuotientReduction`](RealLargeLanglandsQuotientReduction.md)
   uses irreducibility of the target to show that `B` is surjective. Its kernel
   is proper and stable, so `ker B ≤ R`. The image `B(R)` must be zero or the
   entire target. In the latter case each vector of `I(ds)` differs from a
   vector in `R` by a vector in `ker B`, contradicting the properness of `R`.
   Hence `R = ker B`. By surjectivity and intertwining of the enveloping algebra
   actions, `IsMaximallyFaithful π` transfers to
   `IsMaximallyFaithfulModulo (realStandardLie n ds) R`. Step 3 gives `ker B = ⊥`,
   as required.

## Provenance and scope

The target formalizes the large-quotient injectivity consequence for `GL_n(ℝ)`
of Vogan, *Gelfand–Kirillov dimension for Harish-Chandra modules*, Invent. Math.
48 (1978), Definition 6.1 and Theorem 6.2 (p. 89), proof of (a) ⇒ (f) (p. 93),
as explained in `RealGenericLargeReduction.md`. The implemented proof works
throughout in the Library's normalized induction model: character blocks are
signed powers, and nonzero-weight rank-two blocks are Fourier tails in the
corresponding principal series (zero-weight blocks give the full rank-two
principal series). [`StandardModule.md`](StandardModule.md) explains the
comparison with classical induction and its Harish-Chandra module. The
intertwiners and Lie actions in the proof are on these actual function spaces,
not on an abstract substitute or on a postulated comparison isomorphism.

The proof identifies the quotient from the given `B` by the largest proper
submodule theorem; it neither proves nor uses existence or uniqueness of
Langlands data for an arbitrary target module. The unlinked argument uses the
pair criterion in Mœglin, *Representations of GL(n) over the real field*,
§10, Theorem 10b (1997, p. 164), as translated in
`RealLargeStandardIrreducibleReduction.md`; the criterion's sufficiency here
is proved using actual swap maps and the reverse kernel. The linked growth
argument replaces the translation-to-regular-character and τ-invariant argument
in Vogan's proof. Neither that translation argument nor the Speh–Vogan
Theorems 6.15–6.16 cited there are proved or used here. The result assumes
maximal faithfulness as in the exact target; it does not assert the implication
from genericity to maximal faithfulness.
