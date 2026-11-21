# Counting rational points in adelic conjugates of compact sets

Fix an affine group over a number field and a positive-rank faithful matrix
representation given by a closed immersion. For compact sets \(C\) in the full
adelic group and \(K\) in its finite factor, the number of principal rational
points in \(xCx^{-1}\) is at most \(B\operatorname{ht}(x)^d\) whenever the
finite component of \(x\) lies in \(K\). The exponent depends on the field and
representation. The constant can also depend on both compact sets.

The proof embeds the points in the product of the archimedean and finite
matrix entry spaces. The subgroup whose entries are principal adeles is
discrete by the principal-adele isolating neighborhood in each entry.
Conjugation keeps the finite matrix entries in a single compact set, the
image of the product of the compact slices under the continuous conjugation
and entry maps. Submultiplicativity, invariance of height under inversion and
boundedness of height on \(C\) imply that the archimedean entry norm of every
point in \(xCx^{-1}\) is bounded by \(M\operatorname{ht}(x)^2\) for \(M\ge 1\).
The proof then applies `discreteProductSubgroupCounting`. The closed
immersion supplies injectivity of the matrix map, so the same cardinality
estimate holds on the original group.

This derives the compact-finite-component version of the rational counting
estimate used in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series* (Cambridge University Press, 1995), I.2.4(a)(i), pp. 25–26. It gives
the discrete kernel bound used for smoothing on a Siegel domain in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §7.4, part (2) of the lemma on p. 216.
