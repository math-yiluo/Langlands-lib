# The one-coordinate standard Lubin–Tate formal module

`commLaw` lifts tangent addition and negation to actual pointed intertwiners. The formal identities follow because both sides intertwine the same polynomial and agree as linear maps. `scalarAction` applies the same argument to the addition and composition of the lifted scalar endomorphisms. `moduleLaw` supplies the resulting formal module and its natural tangent action.

The defining polynomial is the scalar action of the uniformizer. Applying a coefficient endomorphism that fixes the uniformizer preserves the group law and sends the scalar series for `a` to the series for its image. These facts specialize the standard-polynomial construction in Lubin and Tate, *Formal Complex Multiplication in Local Fields* (1965), §1, Theorem 1, printed p. 382. The coefficient covariance follows by the uniqueness in Lemma 1, printed pp. 381–382.
