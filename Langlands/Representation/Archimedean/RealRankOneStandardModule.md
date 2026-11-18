# Real standard modules in rank one

This internal edge-case derivation supports Task 7158. It states and proves
`RealRankOneStandardIrreducibleStatement`: every list of real blocks of total
rank one has an irreducible actual compact-finite standard module. The
equal-exponent condition is unnecessary in rank one.

A real block has rank one if it is a character and rank two if it is an
induced block. Positivity of block ranks, together with the rank-zero list
lemma, shows that a list of total rank one is a singleton character list.

For a real character datum `d`, let
`characterVector d g = d.character (det g)`. The prescribed signed-power
formula for `d.character` proves smoothness away from determinant zero:
the determinant is smooth, its absolute value is smooth there, and the
positive absolute value admits a smooth complex power. The rank-one
unipotent subgroup is trivial and the principal-series normalization factor
is one. Multiplicativity of the given character therefore gives the
principal-series transformation law. There are no induced blocks, hence
no Fourier vanishing conditions. Right translation multiplies this
character vector by a scalar, so its compact translates span one line.

Every matrix in `GL₁(ℝ)` is diagonal. The principal-series transformation
law at the identity consequently gives
`f(g) = characterVector d g * f(1)` for every standard-module function `f`.
Evaluation at the identity is thus a complex linear equivalence with `ℂ`,
whose inverse sends `c` to `c • characterVector d`. The character vector
has value one at the identity, so this space is nonzero. Each nonzero
subspace contains a vector `f` with `f(1) ≠ 0`; every vector `g` is the
scalar multiple `g(1)/f(1)` of `f`. All complex subspaces are therefore
zero or the whole space, proving irreducibility for the actual compact
and Lie actions.

The rank-one list reduction uses the shared `RealBlockRankOne` lemma.
The proof uses the Library's actual standard-module and character
definitions and smoothness lemmas. It uses no positive-form, R-group,
Langlands quotient or classification theorem. Higher-rank irreducibility
remains a separate obligation.
