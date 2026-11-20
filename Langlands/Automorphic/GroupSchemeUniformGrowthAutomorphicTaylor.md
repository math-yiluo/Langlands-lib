# Automorphy of Taylor vectors of regular automorphic curves

`adelicAutomorphicTaylorCoefficient` packages a coefficient of a weakly holomorphic uniform-growth curve as an actual adelic automorphic form, assuming the curve takes automorphic values on a nonempty open subset of its connected holomorphy domain. The coefficient already has the original smoothness, left rational invariance, open finite level, and growth exponent.

Point evaluations of each compact translate are scalar tests at translated points. Point evaluations of central derivatives are continuous linear scalar tests in the weighted derivative topology. The Taylor coefficient theorem identifies the corresponding orbit profiles, and holomorphic finite-rank descent proves that their spans are finite-dimensional. Injectivity of function evaluation transports the resulting finiteness to the actual compact and center actions. The regular values supply compact finiteness directly and center finiteness through the common annihilating ideal on all infinite slices.

For the general linear group, `stableGeneralLinearTaylorCoefficient` uses the existing comparison of group-scheme and matrix forms and the identification of the full stable operator subspace with the form space.

This is a derived argument for the automorphy of the Taylor functions used in Langlands' proof of Proposition 2. It uses the regular automorphic values in the Fréchet continuation formulation of Bernstein–Lapid, Corollary 8.6.
