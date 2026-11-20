# Denominators for operators invariant under ambient restriction in rank one

`RationalOperatorPolePresentation` records a second polynomial numerator and
a pole-factorable denominator, with a global cross-multiplication identity
against the original rational presentation. The data apply to a whole
operator between fixed complex carriers.

`RationalOperatorPolePresentation.ofAmbientInvariant` takes a continuation
and a nonempty ambient open subset of its starting region. The operator on
this subset must be invariant between parameters that differ by restriction
of an ambient unramified character. Integral product coordinates specify
the kernel of the valuation-image map and give it rank at most one.
The fibers of restriction to that kernel are the orbits of ambient
character restriction.

In rank zero all starting operators are equal, so a constant numerator
with denominator one gives the cross identity by polynomial uniqueness.
In rank one the first element of an adapted integral basis generates the
valuation kernel. Equality of that coordinate implies equality of the
starting operators. The coordinate slice gives the new polynomial numerator
and denominator, and the one-variable Laurent factorization supplies its
unitary pole factors.

`DynamicOppositeMaximalLeviRegularity.forwardPolePresentation` and
`reversePolePresentation` apply the construction to the actual compact
standard operators in both orders for a maximal proper dynamic parabolic.
They use the existing adapted kernel coordinates and ambient twist
invariance of the two integral families at the original measures. The
continuations and the nonempty open starting subsets are inputs.

The rank-one dependence after IV.1(13) in Waldspurger (2003), printed
p. 283 / PDF p. 49 (`waldspurger-2003-plancherel`), motivates the
construction. Its Lean proof uses the actual quotient by ambient
character restriction and gives a whole-operator Laurent denominator for
the pole cancellation in Corollary V.2.3 and Lemma V.3.1, printed
pp. 294–295 / PDF pp. 60–61.
