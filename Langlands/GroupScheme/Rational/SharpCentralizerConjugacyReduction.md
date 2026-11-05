# Sharp conjugacy of represented centralizers

`sharpCentralizerConjugacyReduction.{u}` proves the exact proposition
`SharpCentralizerConjugacyReductionStatement.{u}`. The implementation is the
generic product-cancellation lemma described below; the second lemma specializes
it using two explicit structural inputs.

This is an internal reduction toward sharp conjugacy of maximally split maximal
tori over the maximal unramified extension. It applies over an arbitrary field
`k : Type u`, with arbitrary actual maps and supplied representatives of the
whole-group centralizers on all test schemes.

`exists_range_conjugacy_of_centralizer_product` starts with ordinary rational
conjugacy `a ≫ Int(g) = eA ≫ a'` of two commutative subgroup maps and a product
decomposition `g = p(c) j(z)`. The centralizer representative `j` implies that
`j(z)` fixes `a` under inner conjugation. The formula
`Int(p(c) j(z)) = Int(j(z)) ≫ Int(p(c))` therefore gives the same conjugacy square
with `p(c)` in place of `g`. Transport of the full centralizer along that square
makes `j ≫ Int(p(c))` a representative of the centralizer of `a'`. Uniqueness
of representatives gives an actual isomorphism of the supplied source groups,
compatible with their inclusions. The conjugating point has the explicit range
witness `c`. No surjectivity of rational points of `p` is assumed or inferred.

`exists_cover_conjugacy_of_maximal_split_centralizers` applies the first lemma to
maximal split tori, using `MaximalSplitTorusConjugacyStatement` and
`SimplyConnectedCentralizerProductStatement` as explicit premises. It retains an
arbitrary supplied simply connected derived cover. These two premises remain
unproved by this module.

The provenance is the minimal-Levi conjugacy argument used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Fact 2.6.22 and Lemma 2.6.24,
printed pp.104–105 (PDF pp.135–136), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The implemented argument uses the
Library's product-statement interface and uniqueness of actual centralizer
representatives. The 2024 corrections, Section 2.6, PDF pp.24–25, concern
the subsequent valued-field conventions; this conditional reduction uses no
valued-field assumptions. It proves neither the two structural premises nor
quasi-splitness or the identification of a maximally split maximal torus with
the centralizer of a contained maximal split torus.
