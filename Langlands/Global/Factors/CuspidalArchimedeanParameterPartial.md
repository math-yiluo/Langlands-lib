# Complex-place parameters and real parameters for GL₁

`CuspidalArchimedeanParameterPartialStatement` gives standard-module parameters for actual cuspidal realizations at every complex place in any positive rank and at every real place in rank one. The number field has compact adele quotient. The proof also supplies `exists_rankOne_realPlaceParameter` for an irreducible rank-one operator realization.

At a complex place the proof takes the generic irreducible admissible local component of the cuspidal realization. It applies `complexGenericStandardParameter` and composes its embedding with the embedding of the component. This is the complex branch of the published totally complex parameter-existence proof. The construction at an individual complex place works over any number field in the statement.

In rank one, Schur's lemma gives scalar actions of \(-1\) in the orthogonal group and the identity matrix in the Lie algebra. The compact scalar squares to one, giving the parity. The Lie scalar gives the complex exponent. The resulting real character is the sign to that parity times the absolute value to that exponent. Every vector of its rank-one standard module is determined by evaluation at the identity. Multiplying that evaluation by a fixed nonzero realized vector gives the injective intertwiner. The compact and Lie intertwining identities follow from the two scalar actions.

This result derives the indicated existence clauses of `CuspidalPairPoleStatement`. It reuses the Library's complex generic standard-parameter theorem and the rank-one character and scalar calculations in `RealRankZeroParameter` and `RealRankZeroPlace`. The character coordinates at the infinite places follow Jacquet 2009, Appendix 16.1, author-posted pp. 109–110.
