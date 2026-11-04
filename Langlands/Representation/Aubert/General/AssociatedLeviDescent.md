# Left descents and conjugation at the inverse longest representative

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This module proves three Coxeter facts about the inverse longest representative
`w = (longestRep cs I)⁻¹`, with associated subset
`I' = associatedSubset cs I`. All declarations are theorems in the namespace
`Langlands.Aubert.General.CorrectedFiltration`. The last three restate the
first three at the grade `associatedGrade cs I`, the position of `w` in the
decreasing-length enumeration (module `AssociatedLeviSupport`). In that form
they are exactly the premises `hconj₀`, `hR₀` and `hD₀` of the conditional
top-degree graded surjectivity lemma
`JacquetComplex.gradedDifferential_surjective_top_of_leftDescentSet_eq`
of Worker 1252 (module `CorrectedGradedTopSurjectivity`), at
`i₀ = associatedGrade cs I` and `K₀ = I'`. The theorem
`TerminalJacquet.associatedGradedExactnessTarget_of_targets` (module
`RationalAssociatedLeviReduction`) applies that lemma with these premises to
obtain the top-degree graded surjectivity hypothesis (`hsurj`) of the
conditional associated-Levi comparison in `AssociatedLeviLongestRep`. This
module proves nothing about representations.

Provenance: derived and internal. Classically `w = w₀ w_{0,I}` is the longest
element of the minimal right `W_I`-coset representatives, `I' = w₀ I w₀`,
`W_{I'} = w W_I w⁻¹`, and the left descent set of `w` is `S \ I'`. The
proofs use only published Coxeter results of the Library:

* `associatedSubsetLaws_proof` (`RelativeWeylAssociatedSubsetProof`);
* `minimalityLengthCriterion_proof`;
* `conj_simple_of_left_descent_mul_simple` (`RelativeWeylLongestSurvivorProof`),
  a form of Deodhar's lemma;
* `leftDescentSet`, `mem_leftDescentSet` and `right_length_lt_of_isMinimal`
  (`CorrectedGradedContraction`);
* `isMinimal_associatedSubset`, `eq_inv_longestRep_of_isMinimal` and
  `rankOrderedElement_associatedGrade` (`AssociatedLeviSupport`).

## Conventions

`cs : CoxeterSystem Mx W` is a Coxeter system on a finite group `W`, indexed
by a finite type `ι`. `ℓ` is `cs.length` and `s_j` is `cs.simple j`.
`standardSubgroup cs J` is `W_J`. `leftDescentSet cs x` is the set of `j`
with `¬ ℓ(x) < ℓ(s_j x)`. `S` is `Finset.univ`. `IsMinimal cs J I x` means
`ℓ(x) ≤ ℓ(a x b)` for all `a ∈ W_J` and `b ∈ W_I`.

## Statements and proofs

* `mem_standardSubgroup_associatedSubset_iff`: for every `a`,
  `a ∈ W_{I'} ↔ w⁻¹ a w ∈ W_I`. The third component of
  `associatedSubsetLaws_proof` says that `W_{I'}` is
  `conjugateStandardSubgroup cs I w`, the image of `W_I` under conjugation by
  `w`. Both directions unfold this image.
* `length_lt_inv_longestRep_mul_simple`: `ℓ(w) < ℓ(w s_j)` for every
  `j ∈ I`. This is `right_length_lt_of_isMinimal` applied to
  `isMinimal_associatedSubset`, i.e. `IsMinimal cs I' I w`.
* `leftDescentSet_inv_longestRep` (needs `DecidableEq ι`):
  `leftDescentSet cs w = S \ I'`.
  * If `j ∈ I'`, the left half of the minimality criterion for
    `IsMinimal cs I' I w` gives `ℓ(w) < ℓ(s_j w)`, so `j` is not a left
    descent.
  * Let `j ∉ I'` and suppose `ℓ(w) < ℓ(s_j w)`. Put `x = s_j w`. First,
    `x` is right-`I`-minimal. Otherwise `ℓ(x s_i) < ℓ(x)` for some `i ∈ I`.
    After inversion this says that left multiplication by `s_i` shortens
    `w⁻¹ s_j`. Since `w⁻¹ = longestRep I` is left-`I`-minimal (the inverted
    right minimality of `w`), `conj_simple_of_left_descent_mul_simple`
    gives `w⁻¹ s_j w = s_i`. Then `s_j = w s_i w⁻¹`, so `j` lies in
    `simpleImage cs w I = I'`, a contradiction. By
    `minimalityLengthCriterion_proof`, `IsMinimal cs ∅ I x` holds. Since
    `ℓ(w) ≤ ℓ(x)`, `eq_inv_longestRep_of_isMinimal` gives `x = w`, which
    contradicts `ℓ(w) < ℓ(x)`.

## Forms at the grade `associatedGrade cs I`

These need `DecidableEq W`. Write `w_{i₀}` for
`Support.rankOrderedElement cs.length (associatedGrade cs I)
(associatedGrade_lt cs I)`. Each statement rewrites `w_{i₀}` to `w` by
`rankOrderedElement_associatedGrade` and applies the corresponding statement
above.

* `mem_standardSubgroup_associatedSubset_iff_rankOrderedElement`:
  `a ∈ W_{I'} ↔ w_{i₀}⁻¹ a w_{i₀} ∈ W_I` for every `a` (premise `hconj₀`).
* `length_lt_rankOrderedElement_associatedGrade_mul_simple`:
  `ℓ(w_{i₀}) < ℓ(w_{i₀} s_j)` for every `j ∈ I` (premise `hR₀`).
* `leftDescentSet_rankOrderedElement_associatedGrade` (needs
  `DecidableEq ι`): `leftDescentSet cs w_{i₀} = S \ I'` (premise `hD₀`).
