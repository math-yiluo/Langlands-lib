# Density of square Schwartz tests of finite left unitary span

In `ComplexUnitarySchwartzDensityStatement`, a square Schwartz test has
finite left unitary span if the functions `X ↦ Φ(k⁻¹ X)` span a finite
dimensional complex space as `k` varies in the unitary group. Such tests
are dense in the Schwartz topology on complex square matrices. Each
Schwartz test is consequently the limit of a sequence of these tests.

A unitary left translation is a real continuous linear map, and its
inverse depends continuously on the unitary matrix. Compactness gives
a uniform lower bound for all the pullbacks. The compact average theorem
then approximates any compactly supported Schwartz test by pullback
averages with polynomial weights in the unitary entries and their
conjugates. The Library's Stone–Weierstrass theorem gives the required
uniform density of those weights.

For a polynomial weight `w`, translating its average by `u` replaces
the weight by `v ↦ w(u⁻¹ v)`. This function of `(u, v)` is a finite sum
of separated terms. The integrals of their second factors supply a
finite dimensional space containing all the translates of the average.
Compactly supported Schwartz density gives the conclusion for every
Schwartz test.

This is an internal approximation step for the unitary-finite square
tests in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2,
pp. 56–57.
