# Families with one finite compact source

`ArchimedeanGL.SmoothFamily F n ι` is the product of the actual archimedean smooth spaces with the topology of locally uniform convergence of every enveloping derivative in each coordinate. Right translation and its restriction to the standard compact act in every coordinate. The compact action obeys the actual enveloping covariance law.

`compactGenerator_mem` shows that a finite-dimensional invariant space of these families is stable under the actual differentiated compact action. Along a compact tangent curve the difference quotients converge at every evaluation in every coordinate. The evaluated image is a closed finite-dimensional subspace of the product of scalar function spaces. Injectivity of evaluation gives stability for real tangent directions, and complexification gives stability for all compact Lie generators.

`exists_continuous_source` replaces any finite-dimensional algebraic source of a compact intertwiner into a smooth family by its same image in the family, expressed in a finite basis. Joint continuity of the product action restricts to the image and transfers through the basis. In particular, an algebraic source can be used even when continuity is available only on its image.

This is an internal construction for simultaneous reproduction of fixed-level automorphic forms. It extends the one-function compact orbit and tangent-curve arguments in `ArchimedeanCompactOrbitSource.lean` and `ArchimedeanCompactGroupFiniteProof.lean` to families. The use of a fixed finite compact source and simultaneous convolution comes from Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §1.6 (2), p. 191, and §4.3 (i), p. 195.
