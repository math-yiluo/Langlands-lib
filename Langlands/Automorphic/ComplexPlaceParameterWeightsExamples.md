# Worked complex-place normalization examples

This module checks the coordinates of actual continuous characters constructed
by the published `Langlands.Archimedean.characterOfParams`. All declarations
below are in `Langlands.Automorphic.ComplexPlaceParameter.Examples`.
These are coordinate examples; no embedding into a standard module or an
automorphic class is asserted.

`rho_one` proves `rho 1 i = 0`. `rankOneData` is the singleton with weight
`3` and polar exponent `1/2`. Its exponent coordinates are
`1/2+3/2=2` and `1/2-3/2=-1` (`rankOne_exponents`).
The constant highest weights `2` and `-1` match (`rankOne_matches`), and
the list satisfies `IsClozelRegularAlgebraic 1` (`rankOne_regular`), with
integer witnesses `p=2`, `q=-1`.

`rho_two` computes `(1/2,-1/2)`. `rankTwoData` consists of the two
weight-zero characters with exponents `1/2` and `-1/2`. Each exponent list
is `(1/2,-1/2)` (`rankTwo_exponents`); these are the shifted coordinates
of highest weight `(0,0)` at both embeddings (`rankTwo_matches`).
The integer coset witnesses are `(0,0)` for the first block and `(-1,-1)`
for the second; each exponent list has distinct entries (`rankTwo_regular`).
In contrast `twoTrivialData` uses two copies of `characterOfParams 0 0`.
Their repeated coordinates fail regularity (`twoTrivial_not_regular`).
This distinguishes the shifted highest-weight-zero coordinates from a list
of two trivial parameter characters.

`orientationData` consists of weight-one characters with exponents `2` and
`-1`. Their z coordinates are `(5/2,-1/2)` and their conjugate-z coordinates
are `(3/2,-3/2)` (`orientation_exponents`). Subtracting `(1/2,-1/2)` gives
the respective highest weights `(2,0)` and `(1,-1)`
(`orientation_matches`). The coset witnesses are `(p,q)=(2,1)` and
`(-1,-2)` and both coordinate lists have distinct entries
(`orientation_regular`).

`embedding_false_reads_z` and `embedding_true_reads_zBar` explicitly apply
the existing `ArchimedeanGL.embeddingComponent_inr_false` and
`ArchimedeanGL.embeddingComponent_inr_true` over any number field of
universe `uF`. `orientationHighestWeight` assigns `(2,0)` to the false
index at every complex place and `(1,-1)` to the true index; it chooses
zero weights at real indices. `orientation_matchesGlobal` checks the
global matching relation with this orientation. It does not assert that
these weights give a particular character of the global enveloping center.

The proofs unfold the coordinate definitions, use finite-list and
`List.ofFn` calculations, prove rational identities with `norm_num`, and
give explicit integer coset witnesses. The permutation conditions in
these examples hold by equality of the displayed lists. The orientation
lemmas directly reuse the published component theorems.

The mathematical conventions and original-source correspondence are
documented in [ComplexPlaceParameterWeights](ComplexPlaceParameterWeights.md):
Clozel (1990), Définition 1.8, Définition 3.12 and the proof of
Théorème 3.13, printed pp.89–90 and111–113, registered source
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`.
The selected numbers, lists and their calculations are internal worked
examples, not claims attributed to that source.
