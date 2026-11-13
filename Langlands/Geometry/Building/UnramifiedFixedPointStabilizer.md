# Coefficient stability of the full stabilizer at a fixed point

This is an internal algebraic helper for the prescribed-point integral-model
route. It proves stability of the full character-kernel stabilizer, but does
not construct an integral model or a torus through a building point.

For fields \(k\subset K\), an arbitrary group scheme \(G/k\), a valuation \(v\)
with values in any linearly ordered commutative group with zero, and a
coefficient automorphism \(\sigma\) preserving \(v\),
`rationalConjugate_mem_characterValuationKernel_iff` proves
\[
  \sigma(g)\in G(K)^1 \quad\Longleftrightarrow\quad g\in G(K)^1.
\]
Here \(G(K)^1\) is the published `characterValuationKernel`: every actual
rational character of \(G_K\) evaluates to an element of valuation one.
Neither commutativity, reductivity, affineness, nor splitness is required.

For preservation, choose a rational character \(\chi'\) whose Galois
transport by \(\sigma\) is the tested character \(\chi\). Such a character
exists by `rationalCharacters.galoisRepresentation_self_inv`. The published
`Langlands.GroupScheme.rationalCharacterEval_rationalConjugate_of_eq` then
identifies evaluation at the conjugated point with the coefficient
automorphism applied to the evaluation of \(\chi'\) at the original point.
Valuation invariance and the original character-kernel membership make this
value one. Choosing \(\chi'\) by existential elimination keeps it a separate
variable throughout this calculation. Reflection follows by applying the same
preservation argument to \(\sigma^{-1}\), whose valuation invariance follows
from that of \(\sigma\), and using the published composition and identity laws
of `rationalConjugate`.

For any \(G(K)\)-set \(Y\) and a permutation \(\alpha\) satisfying
\(\alpha(gz)=\sigma(g)\alpha(z)\),
`rationalConjugate_mem_characterKernel_inf_stabilizer_iff` proves transport
of \(G(K)^1\cap G(K)_y\) to \(G(K)^1\cap G(K)_{\alpha(y)}\). This combines
the character-kernel equivalence with injectivity of \(\alpha\).

`UnramifiedFixedPointStabilizerStatement` specializes this to the actual
maximal unramified field of any nonarchimedean local field \(F\). It quantifies
over any group scheme \(G/F\), any semilinear permutation action on a
\(G(K)\)-set in the same universe, and a point fixed by every coefficient
automorphism. At that point, coefficient conjugation preserves and reflects
membership in \(G(K)^1\cap G(K)_y\).
`unramifiedFixedPointStabilizer` proves the statement using the published
`Langlands.Geometry.Building.MaximalUnramified.valuation_galois`.
The statement and proof allow arbitrary universes and either characteristic.

For the supplied root-valuation quotient,
`KPApartmentData.rationalConjugate_mem_characterKernel_inf_reducedFixer_iff`
uses the existing actual coefficient action. Its point stabilizer factor
is transported by the published
`KPApartmentData.galoisQuotientAction_smul_eq_iff`. This specialization requires
the existing affine-group, monomorphism and Galois-stability hypotheses; it
adds no apartment comparison or building-descent assertion.

Finally,
`Langlands.GroupScheme.IntegralModel.exists_descent_of_fixedPoint_integralPoints`
is an explicitly conditional corollary. Given a smooth model over the maximal
unramified integers whose integral-point image equals
\(G(K)^1\cap G(K)_y\), the proved stability verifies the invariance premise
of `UnramifiedSmoothModelDescentStatement`. If that descent statement is
supplied, the corollary returns a smooth model over the integers of \(F\)
and an isomorphism from its unramified base change to the supplied model,
over the identity on the generic group.

The inputs are published in `KPZeroSubgroups`,
`Rational.CharacterGaloisAction`, `GaloisApartmentQuotientAction`,
`UnramifiedOmegaGaloisStable`, and
`IntegralModel.UnramifiedSmoothDescent`. This helper is an internal deduction
from their character-transport identities, coefficient permutations and
valuation invariance; no separate claim from the literature is formalized.
The smooth-descent statement remains a hypothesis of the final corollary.
The exact unconditional task objective
`Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement`
remains unproved: the necessary point-model construction, residue-torus
geometry and maximal split-torus existence at the prescribed point are
retained obligations.
