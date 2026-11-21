# A family containing the ordinary normalized covering and residue tests

`NormalizedEqualPoleTest` records an actual test standard outside the chosen finite set and an entire normalization of its ordinary partial integral. Using all such data as the index type retains both the pole witness and any supplied nonzero test with exponential strip growth. A covering collection of tests implies pointwise nonvanishing for this family.

`exists_equalNormalizedFamily_of_local` fixes two split-centre-trivial cuspidal realizations, their presentations with irreducible admissible finite components, the finite Euler factor choice, and the supplied real and complex parameters. The nontrivial unitary adelic additive character is trivial on the diagonal field. The supplied slice comparisons use that character and its inverse. The local generation assumptions supply covering tests through the specified Whittaker slice model ranges. The local continuation assumptions give the test with nonzero origin values and the actual conjugate vector pair when the realizations are of that form. Choose a finite set containing the additive support and exceptional places, enlarged for the conjugate witness when applicable. The premise provides a nonzero normalized test of exponential strip growth at any finite set containing the two exceptional sets and the finite additive support, so it applies at the selected set. Each entire normalized value multiplied by the prescribed archimedean and retained finite factors matches the partial integral on a right half-plane.

This is an internal construction of the equal-rank family consumed by the pole reduction. The origin test and the covering tests use the ordinary global integral of J. W. Cogdell, *Analytic Theory of L-Functions for GL(n)*, chapter 9 of Bernstein and Gelbart, eds., *An Introduction to the Langlands Program*, Birkhäuser, 2004, Theorem 4.1, printed pp. 218–221.

`exists_equalNormalizedFamily_of_local_at` uses real continuation and generation only in the presence of a real place. Its fixed-field implementation assembles both the covering and conjugate residue tests. The import of `CuspidalPairPoleEqualLocalTests` supplies the covering family construction directly.

`exists_equalNormalizedFamily_with_test_of_local_at` takes only the equal-rank
continuation clauses. It passes the assembled covering tests, the exceptional
set inclusions and the finite additive support to a callback that chooses a
normalized member satisfying the specified predicate. The family contains that
member as well as the conjugate residue witness. For the strip estimate,
`exists_equalNormalizedFamily_of_local_at` specializes the predicate to
nonvanishing somewhere and exponential strip growth.
