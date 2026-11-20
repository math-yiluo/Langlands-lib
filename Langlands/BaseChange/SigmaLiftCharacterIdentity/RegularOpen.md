# Openness of the σ-regular locus from norm existence

The compact neighborhood in the forward argument of Henniart–Lemaire (2011),
II.2.11, lies in the σ-regular locus. This lemma proves the openness used
there from the existence clause of the cyclic norm lemma in I.2.2. It
works over nonarchimedean local fields in any characteristic.

Take the resultant of the characteristic polynomial and its derivative
with degree bounds \(n\) and \(n-1\). The Sylvester matrix then has fixed
size, so its determinant is continuous in the coefficients. For a
monic characteristic polynomial over the base field, the excess degree
bound in the derivative multiplies the usual resultant by a power
of the leading coefficient, which is one. Hence this resultant is
nonzero exactly when the polynomial is separable.

For an associated pair, conjugacy and compatibility of the Sylvester
matrix with ring maps identify the resultant of the cyclic norm with
the base change of the ordinary resultant. The base field injects
into the nonzero cyclic algebra. With existence of an associated ordinary
element for each twisted element, the σ-regular locus is the
inverse image of the complement of zero under this continuous
resultant of the cyclic norm. `sigmaRegularOpen_of_cyclicNormLemma`
uses precisely the existence clause to supply `SigmaRegularOpenStatement`
for the forward reduction.
