# Essential square integrability in the local sigma-lift vocabulary

`determinantNorm_eq_padic` identifies the determinant characters through the equality of the two residue-normalized absolute values. The essential square-integrability predicates then use the same real determinant twist, central quotient and Borel Haar measures. This gives `isEssentiallySquareIntegrable_iff_padic`.

`padicSupercuspidalEssentialSquareIntegrability` transports the supplied supercuspidal action to the canonical p-adic topology and applies the Library's result that a supercuspidal representation is essentially square-integrable there. The supplied and canonical topologies agree. The determinant characters agree as well, since both use the canonical norm raised to the field degree. Thus the square-integrability property holds in the supplied topology and the local sigma-lift vocabulary.

This bridge supplies the essentially square-integrable member required to apply Henniart–Lemaire (2011), II.4.8, Lemme (2), when cuspidal sigma-lift existence provides a supercuspidal representative in the fibre.
