# The unequal-rank integrals along a canonical Jacquet family

Fix a compact-finite larger standard vector, fix a smaller Whittaker vector, and vary the larger inducing exponents holomorphically with one complex parameter. The larger canonical Jacquet vector retains the original compact profile. `complexUnequalCanonicalFamily` gives a common right spectral half-plane of absolute convergence and joint holomorphy for both exact unequal-rank integrals when the inducing parameter varies in a bounded disk.

Transfer of the larger standard vector preserves its compact restriction. Its canonical Jacquet family is holomorphic at each group argument. On the image of the closed parameter disk, compactness makes the local simple-root estimates uniform. For the fixed smaller vector, the existing simple-root estimate and left Whittaker covariance give the bound on the full group by Iwasawa decomposition. The existing ordinary and dual integral family theorems apply with these two bounds. Taking the maximum of their thresholds gives the common half-plane.

This is a derived analytic step for continuation out of the chamber. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.1](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`complexUnequalCanonicalFamilyBounds` also supplies a common bound for the absolute values of both raw integrals over each closed spectral strip in the right half-plane and the entire parameter disk. The ordinary and dual majorants are integrable and uniform on each such strip. Their norm integrals bound the raw integrals, using Fubini for the dual integral. The bound has no dependence on the imaginary part of the spectral parameter.
