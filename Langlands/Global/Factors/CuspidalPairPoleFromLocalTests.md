# The pole theorem from the ordinary local tests and completed functional equation

`CuspidalPairPoleFromLocalTestsStatement` is a reduction to two inputs. One is the published completed functional equation. The other is `CuspidalPairOrdinaryLocalInputs`, which combines ordinary local continuation and normalized generation, exponential strip growth of the ordinary archimedean normalizations, and the specified Whittaker slice model comparison over every number field. The growth premises use the real and complex quotient measures chosen by the test construction. The conclusion is exactly `Langlands.Global.CuspidalPairPoleStatement` in the two original universes.

The proof chooses the additive scales and compares the actual local model ranges for the two presentations and the opposite characters. It takes the finite additive characters and self-dual measures from the Library. The equal-rank construction provides a normalized covering family, a member of exponential strip growth, and the conjugate residue witness after a common finite enlargement. The unequal-rank construction provides the covering family and its growth member with the larger rank first. The published global reduction then supplies the exact pole criterion and strip bounds, using the completed functional equation for the left vertical lines.

The local assumptions concern Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, §2, author PDF pp. 6–10. This is an internal derivation of the route through ordinary global integrals in J. W. Cogdell, *Analytic Theory of L-Functions for GL(n)*, chapter 9 of Bernstein and Gelbart, eds., *An Introduction to the Langlands Program*, Birkhäuser, 2004, Theorems 4.1–4.2, printed pp. 218–222. The completed equation and the stated ordinary local inputs are premises.

## Totally complex fields

`CuspidalPairPoleTCFromLocalTestsStatement` keeps the completed equation over
totally complex fields, complex ordinary continuation and generation, complex
normalized strip growth, and the specified actual slice comparison over each
such field. Its conclusion is the published `CuspidalPairPoleTCStatement`.

The proof fixes the number field before assembling the ordinary tests. There
are no real places, so every use of real local analysis has an empty index.
Complex local normalization gives the covering families in both rank orders.
The equal-rank family includes the conjugate residue witness. The common
continuation theorem handles the rank comparison and supplies the bounded raw
integral and its entire normalized factor of exponential strip growth. The
totally complex reduction uses the completed equation for the left boundary
estimate and then applies the vertical-strip argument.

This is a specialization of the implemented ordinary-test and completed
functional equation route. The equal-rank integral and residue argument are
in Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3, printed
pp. 208–211, and §§4.1–4.2, pp. 219–222. The local hypotheses correspond to
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Theorems 2.1, 2.3,
2.6 and 2.7, author pp. 6–10.
