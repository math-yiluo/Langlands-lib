# The reductive centralizer and its actual split component

`ActualCentralizerStructureStatement` states that the algebraic centralizer
of a maximal split torus is connected reductive and that the same torus,
factored through this centralizer, is its split component. It ranges over
every field `F`, every connected reductive `G`, and every actual maximal split
torus `i : S → G`. In particular, it applies over nonarchimedean local fields
of both characteristics without a split or quasi-split restriction on `G`.

The closed subgroup `j : Z → G` must represent `torusCentralizer i`, whose
membership condition tests commutation after every refinement of every test
scheme. The actual morphism `s : S → Z` must satisfy `s ≫ j = i`.
Consequently, the proposition concerns the whole algebraic centralizer,
rather than only points commuting over the base field. Neither connected
reductivity of `Z` nor `IsSplitComponent s` is a hypothesis.

The conclusion uses the existing definitions without changing their meaning.
`IsSplitComponent s` says that `s` is a closed central split subtorus of `Z`
and is maximal among such subtori. This is an algebraic structural statement;
it does not assert existence of a representing model `Z` or its factorization
`s`. It states the conclusion for every supplied pair that meets these actual
representation and factorization conditions.

The provenance is a derived specialization of the following original
literature. Milne, *Algebraic Groups* (2017), Corollary 17.59,
printed p.371/PDF387, states reductivity of the centralizer of a torus, with
smoothness and connectedness in its proof. Paragraph 17.72,
printed p.376/PDF392, records smoothness and connectedness over an arbitrary
base field. For the split-component conclusion, `S` is central in its own
centralizer by the all-test-scheme commutation condition. Its split maximality
in `G` implies maximality among central split subtori in `Z`: composing any
larger central split subtorus with the closed immersion `j` gives a split
subtorus of `G` through which `i` factors. This explains the mathematical
derivation; the module only states the target and does not implement its proof.
The registered author errata snapshot of 2 November 2026 has no correction
to Corollary 17.59 or paragraph 17.72.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.6(d),
printed p.103/PDF134, constructs the character valuation through a connected
reductive group's maximal central split torus. Section 5.2,
printed p.187/PDF218, applies it to `Z = Z_G(S)` and the same `S`.
The present target makes that structural specialization explicit for the
Library's represented centralizer. It is separate from
`CentralizerValuationComparisonStatement`, which asks for real evaluation
bijectivity, and from `CharacterRestrictionStatement`, which asks for
injective finite-index character restriction given a split component.
The current target supplies neither of those conclusions as a proved result.

No valuation image, integral lattice, special vertex, parahoric, maximal
compact subgroup, double-coset parametrization, or representative set is
defined or asserted here. In particular, the target does not compare
`Z(F)^0` with the common character-norm kernel `Z(F)^1`. Those distinctions
remain obligations of the subsequent Cartan and maximal-compact statements.
