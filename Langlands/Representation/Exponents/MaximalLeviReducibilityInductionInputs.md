# The induction inputs of the unitary case of Renard VII.1.3

Lean module: `Langlands.Representation.Exponents.MaximalLeviReducibilityInductionInputs`.

The published module `MaximalLeviReducibilityUnitaryInputs` states, as unproved
propositions, the results of Renard (2026) used in the proof of VII.1.3 (PDF pp. 230–232).
Three of them are about normalized parabolic induction
`i_P^G = leviInductionFunctor p l r hp hr hl hmul` from an actual rational parabolic
`P = M ⋉ U` of a connected reductive group `G` over a nonarchimedean local field `F`.
This module proves those three. Two of the proofs still use published statements that are
not yet proved, and these appear as explicit hypotheses.

## `leviInductionNontrivial : LeviInductionNontrivialStatement`

If `σ` is a nonzero smooth representation of `M(F)`, then `i_P^G σ` is nonzero. This needs
no hypotheses.

Proof. `i_P^G σ` is by definition the published normalized induction
`normalizedInductionFunctor` from the literal point image `P(F) ⊆ G(F)`, applied to the
pullback of `σ` along `leviPointsEquiv` (the topological isomorphism between `M(F)` and its
image in `P(F)`). The pullback has the same carrier as `σ`, so it is nonzero. The published
lemma `continuous_projection_pointImage` shows that the Levi projection `P(F) → M(F)` is
continuous. Given that, the published lemma `nontrivial_normalizedInduction` shows that
evaluation at `1` maps the induced space onto the carrier, using compactly supported local
sections. So the induced representation is nonzero.

## `leviInductionAdmissible_of_quotientCompact`

Renard III.2.3: if `P(F) \ G(F)` is compact, normalized induction preserves admissibility.

Hypothesis: the published `ArbitraryParabolicQuotientCompactStatement`. The proof applies
the published `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement` to the
given parabolic.

## `leviInductionUnitarizable_of_inputs`

Renard IV.2.3: normalized induction of a unitarizable representation is unitarizable.

Hypotheses: four published statements.

* `RationalReductiveUnimodularityStatement`: rational points of connected reductive groups
  are unimodular. It takes `StandardCocharacterStatement` as an argument, so that statement
  is the second hypothesis.
* `ArbitraryParabolicQuotientCompactStatement`: compactness of `P(F) \ G(F)`.
* `ParabolicRootPresentationExistenceStatement`: every parabolic, rational Levi and split
  component of the Levi admit a compatible root presentation.

Proof. Let `b` be an invariant positive form on `σ`.

1. The proved `splitComponentStatement` gives a split component `a` of `M`. The
   existence statement gives a root presentation `pres` of `(p, l, a)`.
2. The published `modularCharacter_of_presentation` (module `ParabolicPresentationUnitarity`)
   turns `pres` and unimodularity of `M(F)` into the identity between Mathlib's modular
   character of `P(F)` and the Haar modulus of conjugation on `U(F)`. This identity is
   Renard V.5.4.
3. The published `leviInductionUnimodularForm` (module `ArbitraryParabolicUnitarity`) takes
   compactness, unimodularity of `G(F)`, this modular-character identity and `b`. It
   returns an invariant positive form on `i_P^G σ`, given by integrating over the compact
   quotient.

The literature route (IV.2.3) is the same: induce the inner product by integration over
`P \ G`. The modular-character identity makes the integrand a well-defined invariant
measure on the quotient.
