# Growth of coefficients of compact-derivative-bounded forms

For a smooth real position principal series, consider a linear form whose
absolute value is bounded by a constant times a finite sum of compact
right-derivative supremum seminorms. `HasCompactDerivativeBound` expresses
this bound using an arbitrary upper bound for each supremum. The size of
the finite family, its derivative words, and its constant are independent
of the vector.

`CompactFunctionalGrowthStatement` gives one polynomial height exponent
for every coefficient of such a form. A coefficient is the form evaluated
on the right translate of a vector. Conjugating the directions in a
derivative word expresses each derivative of the translate at `k` as a
derivative of the original vector at `kg`. The Frobenius matrix norm
bounds each entry of a conjugated direction by a fixed constant times
the height of `g`. Expanding the derivative in matrix units adds at most
one height power per direction. Orthogonality gives the same height at
`kg` and `g`, and the compact-to-height estimate supplies the common
exponent for the underlying principal-series vectors. Applying the
finite seminorm bound to the translate gives the claim.

This estimate provides the common growth exponent in the direction from
a derivative-bounded form to its principal-series coefficients. Comparing
the Library's given K-finite Whittaker maps with continuous forms and
extending those forms along the source inclusion remain proof
obligations of the principal-series reduction.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 3.7 and §11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
