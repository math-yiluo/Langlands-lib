# The spectrum of a closed-ideal quotient

Author: Worker 36.

`Langlands.Analytic.QuotientSpectrumStatement` is a proposition about every
normed commutative ring A. The zero locus of every ideal is closed in the
bounded multiplicative spectrum. For each closed ideal I, pullback along the
actual quotient projection A → A/I is a closed embedding, and its image is
exactly that zero locus. Every point annihilating I descends to exactly one
bounded multiplicative seminorm on the quotient, agreeing on every quotient
representative.

Closedness of I is needed only for the quotient normed-ring structure, not
for closedness of the zero locus. No completeness, nontriviality, scalar-field,
or ultrametric assumption is imposed. In particular, the statement includes
the unit ideal and its zero-ring quotient; it does not assert spectrum
nonemptiness. Its only project import is the independent Definitions helper,
which in turn imports the published spectrum definitions. No proof of the
target or of general spectrum compactness is imported into the statement.

This is a derived consequence of Berkovich's bounded multiplicative spectrum
and evaluation topology (Trieste lectures, 2009, Definitions 1.2.3 and 1.2.5,
p.4) using the quotient-norm convention at the beginning of §2.1, p.7.
The source's Banach setting is generalized to incomplete normed rings here;
only seminorm descent, the quotient norm and evaluation topology are involved.
The result is a statement about topological spectra and does not provide a
structure sheaf, a closed analytic subspace, or an analytic domain.
Registered source: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
