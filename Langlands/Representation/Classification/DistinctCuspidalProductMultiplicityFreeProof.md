# Proof of multiplicity freeness of products of distinct supercuspidal data

This module proves Zelevinsky's Proposition 2.1(c), stated in the Library as
`Langlands.Classification.DistinctCuspidalProductMultiplicityFree.{uF,uV} F T`
in `Classification.DistinctCuspidalProductMultiplicityFreeStatement`.

The theorem is `Langlands.Classification.distinctCuspidalProductMultiplicityFree`.
The module first proves the conditional theorem
`Langlands.Classification.distinctCuspidalProductMultiplicityFree_of`. Its two
hypotheses are, for every rank `n`, the Library propositions
`CuspidalSupport.AssociatedJacquetFiltrationTheorem.{uF,uV} F T n` and
`CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF,uV} F T n` from
`CuspidalSupport.JacquetInductionStatement`. These are parts (b) and (c) of
Bernstein–Zelevinsky 1977, Corollary 2.13, for `GL_n`. The closed theorem
discharges both hypotheses with their published proofs:
`CuspidalSupport.associatedJacquetFiltration` (module
`CuspidalSupport.AssociatedProof`) and
`CuspidalSupport.nonassociatedJacquetSubquotients` (module
`CuspidalSupport.NonassociatedJacquetSubquotientsProof`). Both hold for every
rank, including rank zero, with no extra premise.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ENS (4) 13 (1980), §2.1, Proposition 2.1, printed p.176 / PDF page 13
(source `zelevinsky-1980-induced-ii`). Zelevinsky fixes an ordering `λ` of a
finite set `R` of cuspidal classes. For each such ordering, `Ω(π)` is the
multiset of irreducible factors of the Jacquet modules `r_{P(λ)}(π)`. Part (a):
`Ω(π(λ)) = Ω` is a set, by [BZ77] 2.13(c). Part (b): every composition factor
`ω` has `Ω(ω) ≠ ∅`, and the sets `Ω(ω)` partition `Ω`. Part (c) follows from
(a) and (b). If `ω` occurred twice, additivity of `Ω` would give an element of
`Ω` with multiplicity at least two.

## Implemented proof

The Lean proof follows the same multiplicity count. It does not form the
multisets `Ω`: it works directly with actual filtrations and actual
equivalences. Let `σ` be the external tensor of the factors `A i` and `P` its
upper normalized induction along `B`. `glCuspidalTensor` shows that `σ` is
irreducible and quasicuspidal on the Levi.

1. **Weyl transports (`mem_blockWeyl_of_transport_equiv`,
   `minimalConjugating_eq_of_transport_equiv`).** Suppose the Weyl transport of
   `σ` by a coordinate permutation `v` that conjugates `B` to itself is
   equivalent to `σ`. Then `v` lies in the block Weyl group. The argument
   copies the published `DistinctTensorStabilizerProof`. Each block factor is
   compared through `nonempty_equiv_of_factor_actions`. `cuspidalDatum_eq_of_equiv`
   then shows that the block map fixes every block, by injectivity of the rank
   and class data. For two minimal conjugating permutations `w₁, w₂` from `B` to
   `C` with equivalent transports, apply this to `w₂⁻¹ * w₁`. Uniqueness in
   `minimalConjugatingCosets` then gives `w₁ = w₂`. This is the content of 2.1(a):
   the Jacquet factors indexed by distinct minimal permutations are pairwise
   inequivalent.

2. **Detection (`exists_associated_nontrivialJacquet`).** Let `D` be a nonzero
   smooth subquotient of `P`. The published `minimalNonzeroJacquet` gives a
   standard Levi `C` such that `r_C(D)` is nonzero and quasicuspidal.
   `normalizedJacquetSubquotient` makes it a subquotient of `r_C(P)`. If `C`
   were not associated to `B`, the hypothesis `NonassociatedJacquetSubquotientsTheorem`
   would force it to be zero. Hence `C` is associated to `B`. This is the
   `Ω(ω) ≠ ∅` part of 2.1(b).

3. **Finite composition series.** Every associated `C` lies in
   `JacquetLength.associatedShapes`. The hypothesis
   `AssociatedJacquetFiltrationTheorem` filters `r_C(P)` with graded pieces
   equivalent to the transports of `σ`. Those transports are irreducible
   (`JacquetLength.isIrreducible_transport`). So `r_C(P)` has composition
   length at most the number of minimal conjugating permutations. With
   detection, the published `jacquetDetectingFamilyLength` produces an actual
   finite filtration `s` of `P` with simple graded factors.

4. **Jacquet image filtration (`jacquetImage`, `jacquetImageFiltration`,
   `jacquetImage_quotient_equiv`, `jacquetImageFiltration_graded`).** Every step
   of `s` maps to its image in the normalized Jacquet module `r_C(P)`. These
   images form a filtration `u` of `r_C(P)` of the same length. Each step
   inclusion `U → P` induces an injective map on Jacquet modules. Its image is
   the Jacquet image of `U`. By exactness of the normalized Jacquet functor
   (`normalizedJacquetMap_exact`), the kernel of `r_C(U) → r_C(U/L)` is the image
   of `r_C(L)`. `MultiplicityAdditivityProof.quotient_equiv_of_surjective` then
   identifies each graded piece of `u` with `r_C` of the matching graded piece
   of `s`.

5. **Conclusion.** Suppose graded factors `i ≠ j` of `s` are equivalent. By
   `exists_isSubquotient_graded` and detection, there is an associated `C` with
   `r_C(gr_i s) ≠ 0`. The graded pieces `i` and `j` of `u` are then nonzero and
   equivalent. Let `t` be the filtration of `r_C(P)` given by
   `AssociatedJacquetFiltrationTheorem`; it has simple factors. The published
   `ObjectRepFiltration.exists_equiv_factors_of_equiv_graded` (in
   `Filtration.GradedRepetitionProof`) gives two distinct indices of `t` with
   equivalent factors. These factors are transports by two distinct minimal
   conjugating permutations, which contradicts step 1.

The auxiliary lemma `jacquetImage_quotient_equiv` raises `maxHeartbeats` to
400000 for definitional unfolding of the actual Jacquet quotient maps.

## Dependencies

Imports: the target statement; `Filtration.GradedRepetitionProof`;
`CuspidalSupport.InducedJacquetCount`, `MinimalJacquetProof`,
`JacquetDetectingFamilyLengthProof`, `CuspidalTensorProof`,
`DistinctTensorStabilizerProof`, `AssociatedProof` and
`NonassociatedJacquetSubquotientsProof`. The closed theorem has no
hypotheses beyond the target's own. The module introduces no axioms. Its
declarations use only `propext`, `Classical.choice` and `Quot.sound`.

## Dependency audit

The transitive Library import closure has 442 `Langlands` modules. It
includes the published proofs of the actual p-adic geometric lemma
(`Geometric.GeometricLemmaProof`), the associated filtration (task `6fe38fdd`)
and the nonassociated subquotient vanishing (task `b17b8c8c`). Its only
`Classification` modules are the target statement and the definition and
support modules `Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalContragredientStatement`, `SupercuspidalContragredientAux`,
`Segments`, `ConstituentRelations` and `SupercuspidalSupport`. It contains no
segment Jacquet, multisegment, tempered, square-integrable classification,
quotient coverage or exhaustion module. No Markdown file in the closure cites
any excluded task. So no conclusion or proof successor of the excluded tasks
is used: segment constituents `67279e36`, segment Jacquet equivalence
`ed48ae06`, and `aca8805b`, `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `52e97845`,
`1cb45da2`, `cd8ab97c` and `bf433f0a`. The two-supercuspidal structure task
`ab61f565` is not used. The full cuspidal Jacquet counts remain owned by
tasks `6fe38fdd` (associated filtration) and `b17b8c8c` (nonassociated
subquotients). This module imports their published proofs and does not
reprove them.
