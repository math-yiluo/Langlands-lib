# The ordinary spherical two-block orbital formula

For a regular semisimple element in the standard two-block Levi with coprime block characteristic polynomials, the two block centralizers identify with the ambient centralizer through the block diagonal embedding. The proof takes compatible measures on the two block quotients. Their product is the compatible quotient measure for the Levi product Haar and the product of the block centralizer measures.

The spherical quotient integration formula restricts the orbital function to Levi and radical coordinates. Its scalar accounts for the normalization of the supplied ambient centralizer measure. Ordinary conjugation by the upper radical then makes the linear change of variables `x ↦ x − γ₀⁻¹ x γ₁`. The inverse absolute Jacobian and the inverse half modulus are invariant under Levi conjugation. The normalized radical integral has a finite spherical expansion, and the quotient product and Fubini identify each tensor integral with the product of the two block orbital integrals.

The proof of `OrdinarySphericalTwoBlockOrbitalDescentStatement` chooses a Haar measure on each commutative block centralizer and takes its compatible quotient measure. The supplied ambient centralizer measure is a positive scalar multiple of the transported product measure by Haar uniqueness. This determines the measures and scalar before the test function and its expansion are supplied.

The reduction to `FundamentalLemmaStatement` now uses three premises.

- `RegularEllipticFundamentalLemmaStatement` gives vanishing and matching for regular elliptic elements.
- `UnramifiedBaseChangeHomStatement` gives the base-change maps on the two smaller blocks.
- `AssociatedSphericalTwoBlockOrbitalDescentStatement` gives the formulas at exact block norms with associated block measures and a common scalar.

The ordinary formula is the two-block spherical case of Laumon, *Cohomology of Drinfeld Modular Varieties, Part I* (1996), Proposition 4.3.11. It supplies the ordinary vanishing step in the nonelliptic induction of Arthur–Clozel, Chapter 1, Theorem 4.5, and Henniart–Lemaire, I.6.6.
