# Reduction of the spherical fundamental lemma to regular elliptic elements

`FundamentalLemmaBlockReductionStatement` is the implication from
`RegularEllipticFundamentalLemmaStatement` and
`SphericalTwoBlockParabolicDescentStatement` to the Library's
`FundamentalLemmaStatement`. All three propositions use independently
universe-polymorphic p-adic fields, the Library's spherical base-change
condition, and the same Haar and quotient measure conventions.

The first premise gives ordinary orbital integral vanishing at regular
elliptic non-norms and concordance at associated pairs with regular elliptic
ordinary element. The second premise assumes spherical concordance in all
smaller ranks. It gives vanishing for regular standard two-block elements
with a non-norm block, and concordance for block diagonal pairs with
exact blockwise cyclic norm equalities. The latter clause may also use
identification of the twisted centralizer with the scalar extension of the
ordinary centralizer.

The Lean proof uses strong induction on the rank index. For a nonelliptic
regular semisimple element, a proper characteristic polynomial factor gives
a conjugate in the standard two-block Levi. The blocks are regular
semisimple and their characteristic polynomials are coprime. If the element
is a non-norm, some block of this conjugate is a non-norm. The second premise
then gives vanishing at the conjugate and transport of the compatible
quotient measure gives vanishing at the original element.

At an associated pair, the proof uses the measure association witness and
the change of basis on the ordinary side to arrange an exact norm equality
with the block diagonal conjugate. The algebra of the cyclic norm puts
the new twisted representative in the same standard Levi with exact norm
equalities in its blocks. The regular centralizer identification applies
there. The second premise gives concordance and the conjugation transport
gives the equality for the original associated pair.

This internal reduction formalizes the induction in Arthur–Clozel (1989),
Chapter 1, Theorem 4.5, and Henniart–Lemaire (2011), I.6.6. Its
two-block premise isolates the analytic use of ordinary and twisted
orbital descent and constant-term compatibility with base change. The
conditional result leaves that premise and the regular elliptic premise
as proof obligations.
