# Trace replacement after bounded character separation

`CharacterTraceReplacementStatement` concerns a summable family of complex
trace coefficients with a family of algebra characters at each place. The
characters satisfy a uniform bound at every test, and the conjugates of the
values of any one test are the values of another common test. Suppose all
finite products of the character values give a zero weighted sum for each
elementary test. Suppose also that a zero elementary sum on each fibre of
the character family implies a zero sum for each replacement test on that
fibre, and that the replacement coefficients are summable.

The proof applies `boundedCharacterSeparation` to the elementary sums. It
then uses the replacement implication on each fibre. On a given fibre
every product of character values is constant, so it multiplies the zero
replacement sum by that value. Uniform boundedness gives summability
after multiplying by the product. Regrouping the resulting series by
fibres yields the replacement identity for every finite product test.

This is an algebraic reduction modeled on the spectral argument in
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, § 4, printed pp. 44–46 (PDF pp. 58–60).
The argument there separates the archimedean contributions, replaces
the tests at a finite place, and sums over the archimedean labels. Here
the separating tests are supplied bounded algebra characters and
the replacement on a fibre is a hypothesis.
