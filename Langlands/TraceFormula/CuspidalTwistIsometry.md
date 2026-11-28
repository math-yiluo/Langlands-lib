# The algebraic twist on the cuspidal Hilbert space

`CuspidalTwistIsometryStatement` concerns a connected reductive group scheme \(G\) over
a number field \(F\) with the data of `fullAEL2CuspidalSubmodule`. The statement
assumes `ParabolicDynamicStatement`, affineness and local finite type, a central split
torus \(Z \to G\) with injective finite-index restriction on rational characters, and
right invariance of the canonical Haar measure on the adelic norm-one subgroup. Let
\(\Gamma\) be the positive rational subgroup of \(G(\mathbb A_F)\) and \(\mu\) the
Library's Haar measure on \(\Gamma \backslash G(\mathbb A_F)\).

Suppose an algebraic automorphism induces an adelic group automorphism \(\Theta\) preserving
\(\Gamma\), with measure-preserving inverse on the quotient. The twisting operator
\(I_\Theta\) on \(L^2(\mu)\) is pullback by the inverse quotient automorphism. The statement
supplies a linear isometric equivalence \(U\) of the full almost-everywhere cuspidal space
whose inclusion into \(L^2(\mu)\) agrees with \(I_\Theta\). It satisfies
\(U \pi(a)=\pi(\Theta a) U\), where \(\pi\) is cuspidal right translation.

`cuspidalTwistIsometry` deduces this statement from `groupSchemeTwistCuspidalInvariance`
and `IsotypicTrace.twistOperator_quotientL2RightTranslate`. The forward quotient map
preserves \(\mu\) by inversion of a measure-preserving equivalence. The inverse algebraic
automorphism therefore satisfies the same hypotheses as the original automorphism. Both
pullbacks preserve the cuspidal subspace by `groupSchemeTwistCuspidalInvariance`. Their
composites are the identity by `Lp.compMeasurePreserving_comp_apply`, so the two
restrictions give inverse linear isometries. Applying the covariance identity on
\(L^2(\mu)\) and using injectivity of the inclusion gives covariance on the subspace.
