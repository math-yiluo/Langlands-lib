# Modified supports at the grade of the inverse longest representative

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This module proves Coxeter-combinatorial vanishing facts for the two-sided
modified supports `CorrectedFiltration.modifiedSupport cs J I i` (the sets
`θ_i'` of the corrected support filtration). They concern the grade at which
the inverse longest representative `w = (longestRep cs I)⁻¹` is added. At that
grade only the coordinate whose target is the associated subset
`I' = associatedSubset cs I` survives. These are the vanishing and
concentration hypotheses (`hθ`, `hlow`, `hconc`, `htop`, `hs`, `hKs`) of the
conditional associated-Levi comparison in the module
`AssociatedLeviSurvivingStep`, for its intended instantiation `K = I'`,
`w = (longestRep I)⁻¹` and `s0 = S \ I'`.

Provenance: derived and internal. These are the combinatorial reasons why, in
Aubert's 1996 erratum (p.4690, Remark (1), display (**)), only the cell of the
associated Levi survives in the retained Jacquet cokernel. Classically,
`w = w₀ w_{0,I}` is the longest element of `W^I`, and `I' = w₀ I w₀`. The
proofs use only published Coxeter results of the Library, with no root
system:

* `longestRepresentativeUnique_proof`;
* `mapsIntoSimple_longestRep` (`RelativeWeylLongestSurvivorProof`);
* `minimalityLengthCriterion_proof`;
* `associatedSubsetLaws_proof` and `longestRep_associatedSubset`
  (`RelativeWeylAssociatedSubsetEquiv`);
* the rank-ordered support lemmas of `RankOrderedSupports`.

## Conventions

`cs : CoxeterSystem Mx W` is a Coxeter system on a finite group `W`, indexed
by `ι`. `ℓ` is `cs.length`. `longestRep cs I` is the chosen maximal-length
element of `D(I, ∅)`, the elements `d` with `ℓ(d) ≤ ℓ(a d)` for all `a ∈ W_I`.
`IsMinimal cs J I x` means `ℓ(x) ≤ ℓ(a x b)` for all `a ∈ W_J` and
`b ∈ W_I`. The decreasing-length enumeration `Support.rankOrderedList cs.length`
has length `N`. The support `Support.rankOrderedSupport cs.length i` consists
of its first `i` elements, and `modifiedSupport cs J I i` is the union of the
double cosets `W_J x W_I` contained in it. `S` is `Finset.univ`.

## Coxeter facts

* `eq_inv_longestRep_of_isMinimal`: if `IsMinimal cs J I x` and
  `ℓ((longestRep I)⁻¹) ≤ ℓ(x)`, then `x = (longestRep I)⁻¹`. Proof: `x⁻¹` lies
  in `D(I, ∅)`, so `ℓ(x⁻¹) ≤ ℓ(longestRep I)`. The length hypothesis makes
  `x⁻¹` of maximal length, and `longestRepresentativeUnique_proof` gives
  `x⁻¹ = longestRep I`.
* `subset_associatedSubset_of_isMinimal`: if
  `IsMinimal cs J I (longestRep I)⁻¹`, then `J ⊆ I'`. Proof: for `j ∈ J`,
  minimality gives `ℓ(w) < ℓ(s_j w)`, i.e. `j` is in
  `positiveSimpleSet (longestRep I)`. By `mapsIntoSimple_longestRep`,
  `longestRep I · s_j · (longestRep I)⁻¹ = s_k` for some `k ∈ I`, so `s_j`
  is `w s_k w⁻¹`, and `j` is in `simpleImage w I = I'`.
* `isMinimal_associatedSubset`: `IsMinimal cs I' I (longestRep I)⁻¹`. The left
  inequalities come from `longestRep I' = (longestRep I)⁻¹`, which lies in
  `D(I', ∅)`. The right inequalities come from `longestRep I ∈ D(I, ∅)` after
  inversion. `minimalityLengthCriterion_proof` turns the simple-reflection
  inequalities into two-sided minimality.
* `card_associatedSubset`: `I'.card = I.card`.

## The grade of the inverse longest representative

* `associatedGrade cs I`: the position of `(longestRep I)⁻¹` in the
  decreasing-length enumeration. `associatedGrade_lt`: it is `< N`.
  `rankOrderedElement_associatedGrade`: the element at that position is
  `(longestRep I)⁻¹`.
* `exists_isMinimal_of_mem_modifiedSupport`: a nonempty
  `modifiedSupport cs J I i` contains an `x` with `IsMinimal cs J I x` that
  lies in the first `i` elements. Take a minimal element of the double coset
  of any member; the modified support is two-sided invariant.
* `modifiedSupport_associatedGrade_eq_empty`: for every `J`,
  `modifiedSupport cs J I (associatedGrade cs I) = ∅`. A minimal `x` in it
  precedes `w` in the enumeration, so `ℓ(w) ≤ ℓ(x)`
  (`rankOrderedElement_rank_le`). Hence `x = w`, but `w` is not among the
  elements before it.
* `modifiedSupport_associatedGrade_succ_eq_empty`: if `J ⊄ I'`, then
  `modifiedSupport cs J I (associatedGrade cs I + 1) = ∅`. A minimal `x` in it
  has `ℓ(w) ≤ ℓ(x)`, so `x = w` and `J ⊆ I'`.
* `length_rankOrderedList_le_associatedGrade_succ`: if
  `Complex.terminalDegree I = 0` (so `I = S`), then
  `N ≤ associatedGrade cs I + 1`. Here `W_I = W` forces `w = 1`, and an
  element after `1` in the enumeration would have length `0`, i.e. be `1`
  again.

## The surviving coordinate

With `[DecidableEq ι]`:

* `associatedCoordinate cs I`: the coordinate `S \ I'` of degree
  `Complex.terminalDegree I = |S| - |I|`, as an element of
  `{s : Finset ι // s.card = Complex.terminalDegree I}`.
  `univ_sdiff_associatedCoordinate`: its target `S \ (S \ I')` is `I'`.
* `isMinimal_associatedCoordinate` and
  `associatedSubset_subset_associatedCoordinate`: the hypotheses `hs` and
  `hKs` (with `K = I'`) of the assembly.
* `modifiedSupport_associatedCoordinate_eq_empty`: the hypothesis `hθ`, the
  case `J = I'` of `modifiedSupport_associatedGrade_eq_empty`.
* `modifiedSupport_lower_eq_empty`: the hypothesis `hlow`. If
  `s.card + 1 = Complex.terminalDegree I`, the target `S \ s` has `|I| + 1`
  elements, so it is not contained in `I'`.
* `modifiedSupport_other_eq_empty`: the hypothesis `hconc`. A coordinate
  `s ≠ S \ I'` of the terminal degree has a target of `|I|` elements. If it
  were contained in `I'` it would equal `I'`, and then `s = S \ I'`.

The module proves nothing about representations, Bruhat cells or graded
exactness.
