# The uniform canonical real Jacquet maps

`RealGodementCanonicalModelStatement` gives a specified uniform Whittaker intertwiner on the actual K-finite standard module of every real character list. Its polynomial growth exponent is common to all source vectors at the given inducing exponents.

In rank one the chamber condition is vacuous, so the canonical map is the convergent uniform map. For the induction step the lower rank has a common growth exponent. Each right derivative is another lower coefficient by Lie equivariance, so the same exponent bounds all those derivatives. The first-column bound produces a common upper exponent independent of the lower input and the Schwartz test. Each upper K-finite vector lifts from a finite compact frame, and each generator of that frame has the canonical first-column formula. The functions bounded by the chosen height power form a linear subspace. The generator bounds therefore place the entire canonical upper image in that subspace.

`canonicalJacquetMap_reflectedPair_mem_span` places a canonical upper coefficient and its actual reflected coefficient in the paired column span. Each lower canonical coefficient lies in its uniform model and its reflection lies in the reversed inverse model. The first-column reflection formula gives the Fourier-transformed partner on each compact generator. Linearity of reflection and spanning then give the asserted pair for every upper source vector.

This implements compact generation and reflection for the continued real character coefficients in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2.
