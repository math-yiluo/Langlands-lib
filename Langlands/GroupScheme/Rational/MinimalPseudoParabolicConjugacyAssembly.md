# Assembly of minimal pseudo-parabolic conjugacy from structural inputs

This internal construction follows the containment argument in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Theorem C.2.5, printed page 595 (PDF page 621). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The construction is conditional. It does not prove the published
`MinimalPseudoParabolicConjugacyStatement` without its five structural inputs.
It imposes no reductivity, perfection, infinitude or characteristic assumption.
The universe is arbitrary, and subgroups and their containment are tested on
all relative schemes.

`exists_maximalSplitTorus` is an unconditional supporting consequence of the
published maximal split torus extension theorem. For an affine group scheme
locally of finite type over a field, its identity section gives the trivial
split torus, and extending this torus gives a maximal split torus. Affineness
supplies separatedness, as required for the trivial torus's closed embedding.

`minimalPseudoParabolicConjugacy_of_structure` takes proofs of exactly these
five published propositions:

- `PseudoParabolicSubgroupStructureStatement`, supplying smoothness,
  connectedness and affineness of a pseudo-parabolic source.
- `SplitUnipotentRadicalExistenceStatement`, supplying the actual split
  ground-field radical of that source.
- `PseudoParabolicSplitSolvableEnvelopeStatement`, supplying the closed split
  solvable representative of the split torus and split radical product.
- `SplitSolvableIntoPseudoParabolicStatement`, the full C.2.2 rational
  conjugation and factorization assertion.
- `PseudoParabolicMaximalSplitTorusStructureStatement`, the maximality,
  centralizer containment and C.2.4 minimality criterion.

Given minimal inclusions `i : P ⟶ G` and `j : Q ⟶ G`, the proof first chooses
a maximal split torus `s` of `P`, a representative `z` of its split radical,
and their split solvable envelope `h`. C.2.2 supplies an actual rational point
`g` and a factorization of the conjugate of `h ≫ i` through `j`.

The implemented proof keeps `P` fixed and instead replaces `j` by
`j' = j ≫ (G.innerIso g).inv`. This is equivalent to the source's replacement
of `P` by a rational conjugate. Ambient transport preserves minimality of `j'`.
Postcomposing the supplied factorization by the inverse inner automorphism
puts both `s ≫ i` and `z ≫ i` inside `j'` on every test scheme.

The C.2.4 input makes `s ≫ i` maximal split in `G`. Its containment allows an
actual lift into `Q`, maximal split there. Applying the centralizer part of the
same input to this lift puts the whole centralizer of `s ≫ i` inside `j'`.
The product criterion applied to minimal `P` now puts `i` inside `j'`: both
product factors lie there, and membership descends along the supplied fppf
cover into the closed represented subgroup. Minimality of `j'` gives equality
of subgroup images and an actual source isomorphism. Composing the resulting
identity-point conjugacy with conjugation by `g` gives the required conjugacy
of `i` and `j`.

`minimalPseudoParabolicConjugatorOfStructure` uses classical choice on this
proof to return an actual rational point, an actual source isomorphism, and
their compatibility equation. The five structural proofs remain explicit
arguments of the definition. The construction and its conditional supporting
theorem supply no proof of these prerequisites, so this unit alone does not
complete the conjugacy proof task.
