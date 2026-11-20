# Uniqueness of cuspidal weak induction from Euler rigidity

`WeakInductionUniquenessStatement` is the uniqueness assertion for two supplied cuspidal weak inductions of the same rank and the same upstairs cuspidal class. It applies to any extension of number fields in the Library's weak induction relation. That relation already requires the downstairs rank to be the upstairs rank times the field degree.

The proof `exists_sameEulerPolynomials_of_isWeakInductionOf` starts with the two pairs of witnessing spectral systems. It presents both upstairs systems on the same cuspidal realization and uses `spectralSystem_sameEulerPolynomials` to compare them. The weak induction relation permits replacing the second upstairs system by the first, so the two downstairs Euler denominators agree wherever both weak matching identities hold. These identities hold together on a cofinite set.

`weakInductionUniqueness_of_cuspidalEulerConstituentRecovery` applies the Euler-polynomial form of Jacquet–Shalika constituent recovery, with a singleton family for each downstairs class. The finite sum over each singleton has the Euler polynomials of its only term. Recovery equates the mixed-rank classes, and the fixed-rank inclusion is injective.

This deduction supplies the rigidity step that identifies a constructed weak induction with a supplied one in the proof of the unique-place supercuspidality consequence of Harris (1998), Proposition 4.8.
