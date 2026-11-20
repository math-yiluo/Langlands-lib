# Diagonal polynomials from individual matrix factors

The Lie inclusion into a single factor of a complex matrix product sends central enveloping elements into the centre of the product. `matrixFactorCenterInclusion` uses commutation with the generators in that factor and the vanishing of brackets with the other factors.

For a singleton product the diagonal projection agrees with `VermaCentral.gamC` from `LowerVermaCentral.lean`. At any diagonal character, `VermaPBW.Psi` evaluates the included diagonal polynomials at that character and kills the strict upper right ideal. This proves the comparison by polynomial extensionality. The general factor inclusion preserves the congruence with the diagonal polynomial, renaming its variables as the coordinates of that factor.

The derived comparison makes the Library's one-matrix finiteness theorem available for the product appearing in Langlands, *On the notion of an automorphic representation* (1979), Lemma 4, printed p. 204.
