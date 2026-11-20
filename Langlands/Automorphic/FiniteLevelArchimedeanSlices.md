# Finite double cosets and archimedean restrictions at open finite level

Borel and Jacquet, *Automorphic forms and automorphic representations* (1979), §4.3, p. 195
(PDF p. 190 of the registered `borel-jacquet-1979-automorphic`), use the finite set of
double cosets of `G(F)` and `G∞ L` and restrict functions to the archimedean slices at its
representatives. This module implements the finite indexing and faithful restriction used
in that step for the Library's adelic general linear group.

The product splitting of the full adelic group absorbs `G∞`, giving the double quotient of
`FiniteAdelicGL F n` by the finite rational image on the left and `L` on the right. The
Library's `exists_siegelDecomposition` puts a rational left translate of any adelic point
in a product of an archimedean torus element and a fixed compact set. Projecting to the
finite group removes the torus factor. The finite projection of the compact set meets
finitely many left cosets of `L`, since `L` is open. Their representatives map onto the
double quotient. The construction applies to every open `L` and every rank.

For faithful restriction, write an arbitrary finite component as `γ_f · b · l`, with `b`
the chosen representative of its class and `l ∈ L`. Right `L`-invariance eliminates `l`.
Rational covariance then evaluates this slice by evaluating the slice at `b` with the
archimedean input translated by `γ∞⁻¹`. These are the two clauses of the existing
`FiniteLevelSmoothSliceFamilies` space. The stabilizer defined here consists of exactly
the rational elements with `γ_f ∈ b L b⁻¹`, as in §4.3 (1).
