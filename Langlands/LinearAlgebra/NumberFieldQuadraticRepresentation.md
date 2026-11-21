# Local-to-global representation by a quadratic form over a number field

A regular quadratic form on a finite-dimensional vector space over a number field represents a scalar if the actual tensor scalar extension represents its image at every finite and archimedean completion. The result includes the zero scalar.

For a nonzero scalar `a`, local representation gives an isotropic vector with first coordinate one in the orthogonal sum of the line of coefficient `-a` and the original form. The actual tensor comparison preserves that sum. The sum is nondegenerate and hence isotropic over the number field by Hasse–Minkowski. An isotropic vector with nonzero first coordinate gives a representation after rescaling. An isotropic vector with zero first coordinate gives a nonzero isotropic vector for the original form, which then represents every value by varying a vector along this isotropic line. The zero vector represents zero.

In dimension at least four, representation at each archimedean completion suffices. At a finite completion the sum with the negative line has dimension at least five, so the local anisotropic dimension bound makes it isotropic. The same global isotropy argument then gives the representation.

Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §5.9, pp. 93–94 (PDF pp. 99–100), uses this representation consequence of Hasse–Minkowski for the quadratic forms in the spin-group argument. The Lean proof reuses the orthogonal sum and isotropic-vector argument of the quadratic isometry reduction.
