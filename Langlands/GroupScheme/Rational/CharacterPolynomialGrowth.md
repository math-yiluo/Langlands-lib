# Polynomial and logarithmic growth of actual rational characters

This internal unit constructs `rationalCharacterSection`, the global regular
function given by the universal value of a rational algebraic character. It
proves polynomial and absolute logarithmic bounds for that character on actual
rational points, using any supplied closed matrix embedding.

Let \(F\) be any nonarchimedean local field, \(G\) an affine group scheme over
\(F\), and \(\rho:G\to\mathrm{GL}_n\) a closed embedding, where the matrix index
type is finite and nonempty. Write \(H(g)\) for the existing
`rationalMatrixNorm F ρ g`, formed from the residue-normalized absolute value of
all matrix and inverse matrix entries. For every actual rational character
\(\chi\), the theorems give

\[
\exists d\in\mathbb N,\ \exists c>0,\ \forall g\in G(F),\quad
|\chi(g)|_F\le c H(g)^d
\]

and

\[
\exists C>0,\ \forall g\in G(F),\quad
|\log|\chi(g)|_F|\le C(1+\log H(g)).
\]

The constants precede the rational-point quantifier. There is no reductivity,
connectedness, splitness or characteristic assumption.

The section is the underlying element of the global unit
`characterEval χ G.X (𝟙 G.X)`. Naturality of character evaluation along an actual
rational point identifies its evaluation through `rationalPointAlgebraHom`
with `rationalCharacterEval χ g`. Applying
`regularFunction_rationalMatrixNorm_powerBound` to this section proves the
first estimate.

For the second estimate, take real logarithms in the first one. Character
values are units, so their normalized absolute values are positive. Also
\(H(g)\ge1\). With
\(C=|\log c|+d+1>0\), the resulting upper bound is at most
\(C(1+\log H(g))\). Apply this same bound to \(g^{-1}\): the character value
inverts and \(H(g^{-1})=H(g)\), so the logarithm changes sign. These two
inequalities prove the absolute value bound.

The final adapter states this same absolute logarithmic bound for the published
positive norm-character family `rationalNormCharacters`, using its exact
identification with the residue-normalized absolute value.

The argument is a direct internal consequence of the actual character
evaluation, closed-embedding regular-function bound and matrix norm laws.
It supplies the character-growth ingredient for later modulus-height
comparisons. It does not construct a parabolic tau representation, identify a
semi-invariant line character with the parabolic modulus, prove the opposite
unipotent height comparison or establish integral convergence.
