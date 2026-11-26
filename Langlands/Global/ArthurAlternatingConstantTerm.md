# Vanishing and invariance of Arthur's alternating constant terms

The sum `alternatingConstantTerm` is the signed combination of constant
terms over the interval from the lower to the upper standard parabolic in
Arthur 2005, §13, equation (13.7), printed p. 71. The sign uses the codimension
of each parabolic index in the full set of simple roots.

Let \(F\) be a number field and \(G\) a connected reductive \(F\)-group.
For standard indices \(R\subseteq S\subseteq\Delta_0\), the vanishing and
invariance results below apply to the signed sum of the constant terms
of a continuous complex-valued function on \(G(\mathbb A_F)\) invariant
under left translation by \(G(F)\). Each constant term is the normalized
Haar average over \(N_P(F)\backslash N_P(\mathbb A_F)\).

A root in the upper index and outside the lower index gives a vanishing
constant term along the ambient maximal parabolic omitting that root. The
proof commutes the outer constant term with the finite sum and applies
`StandardParabolicFamily.constantTerm_constantTerm`. Each term is thereby
replaced by the constant term at the intersection with the maximal index.
The interval is a powerset after adjoining the lower index, and the ambient
sign is a common factor times the powerset sign. Inserting the omitted root
leaves the intersection unchanged and reverses the powerset sign. The
paired terms cancel by `alternatingSum_eq_zero`.

The radical of the upper parabolic belongs to the radical of each term in
the sum. Invariance of the normalized constant term under its own radical
then gives left invariance of the sum under the upper radical on adelic
points. Rational unipotent invariance of each summand gives rational
unipotent invariance of the sum for every standard radical. These
properties let a decay argument use contraction in the upper Levi while
averaging over an ambient maximal radical.
