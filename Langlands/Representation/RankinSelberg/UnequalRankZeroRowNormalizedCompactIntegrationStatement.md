# Normalized compact averages for zero-row unequal-rank integrands

`Langlands.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationStatement.{uF,uV,uW} F T n k`
is a proposition definition for the compact averaging step of the zero-row
unequal-rank Rankin–Selberg integral. It retains every supplied
`T : F.TopologicalData`, independent field and representation universes, and
all `n,k : ℕ`. The smaller rank is `n+1`, the larger rank is
`n+(0+k+1)+1`, and the positive rank gap is `k+1`. Thus `n=0` and `k=0`
are both included.

The statement installs the topology, valuation and local-field instances from
`T`, and the Borel measurable structure on the ambient smaller general linear
group. With the valuation integers of that supplied structure, set

\[
K=\mathrm{GL}_{n+1}(\mathcal O_F),\qquad
\kappa=(\texttt{generalLinearHaar}\ F\ n)|_K.
\]

Precisely, `K` is
`Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`.
The measure `κ` is the restriction to `(K : Set _)` on the ambient group,
as in `EqualRankNormalizedCompactIntegrationStatement`; it is not a measure
on an unipotent quotient. The published normalization
`generalLinearHaar_integralSubgroup` gives this restriction total mass one.

For smooth complex representations `π,σ` on independent carriers `V,W`, a
unitary additive character `ψ`, standard and inverse-character functionals
`ℓ,ℓ'`, and actual coefficient-image elements
`f : (coefficientModel π ℓ).toSubmodule` and
`f' : (coefficientModel σ ℓ').toSubmodule`, the proposition asserts that there
are `m : ℕ`, `z : Fin m → K` and `c : Fin m → ℝ` such that
`0 ≤ c i` for every index and `∑ i, c i = 1`. These data are chosen before
both the arbitrary smaller-group element `g` and the spectral parameter `s`.
For every such `g,s`, let

\[
H_{g,s}(u)=
 f\!\left(\operatorname{diag}(gu,I_{k+1})\right)
 f'(gu)\,|\det(gu)|_F^{\,s-(k+1)/2}.
\]

Here function evaluation denotes the underlying coefficient functions. The
Lean formula is exactly
`unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0 (g * u)`.
Its rectangular argument `0` is the actual matrix in
`Matrix (Fin 0) (Fin (n+1)) F.Carrier`. The published identity
`unequalRankMatrix_zero_rows` identifies the larger-group argument with
`appendIdentity n (0+k+1) (g*u)`, so the formula retains the original
unequal-rank determinant weight and its shift. No replacement integrand is
introduced.

The conclusion has three parts: `H` is integrable against `κ`, and the same
representatives and weights compute both integrals:

\[
\int H_{g,s}(u)\,d\kappa(u)
 =\sum_i (c_i:\mathbb C)H_{g,s}(z_i),\qquad
\int^-\|H_{g,s}(u)\|_e\,d\kappa(u)
 =\sum_i\operatorname{ENNReal.ofReal}(c_i)\|H_{g,s}(z_i)\|_e.
\]

The second formula is an extended nonnegative integral, using the extended
norm. No irreducibility, admissibility or nonvanishing condition is imposed
on the representations, functionals or coefficients. Zero functionals and
zero coefficients are allowed. The statement adds no quotient measure,
Iwasawa, Mellin, rationality or noncompact integrability hypothesis.

## Derived provenance and intended proof route

This is an internal derived adapter motivated by Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), printed p. 391, proof of Theorem 2.7,
the paragraph preceding display (3), and printed p. 394, display (7).
The first passage uses compact finiteness of right translates in the integral
reduction. The second displays the diagonal restriction with exponent
`s-(r-t)/2`; here `r-t=k+1`. The exact normalized finite-average interface above
is not a verbatim theorem from JPSS. These two original pages were visually
read for this formulation. No source-specific errata file was found in the
project's registered literature index or public errata locations.

The intended derivation chooses vectors representing the actual coefficient
images. Smoothness gives open stabilizers of those vectors. Pull the larger
vector's stabilizer back along the actual continuous homomorphism
`appendIdentity n (0+k+1)`, and intersect with the smaller vector's stabilizer.
The resulting open subgroup fixes both coefficient functions under right
translation, uniformly in their arguments. Its intersection with compact `K`
has finitely many cosets in `K`; representatives of these cosets work for all
`g,s`. The determinant of every element of `K` has normalized absolute value
one, so the spectral factor is unchanged throughout this compact variable's
right cosets as well. Haar masses of the cosets supply nonnegative real weights
whose sum is one. A finite partition then gives integrability and both exact
finite-sum formulas, including the extended norm formula.

The published theorem `equalRankNormalizedCompactIntegration` in
`Langlands.Representation.RankinSelberg.NormalizedCompactIntegrationProof`
and the compact integration and finite coset expansion helpers provide
reusable normalization and integration infrastructure. They do not themselves
prove this unequal-rank target: the pullback along the larger-rank embedding
and its compatibility with the actual zero-row integrand still require a
separate proof. This module supplies only the statement; the parent's final
analytic assembly and the separately owned Iwasawa and Mellin work remain
separate obligations.

Source: `jpss-1983-rankin-selberg`, H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, printed pp. 391 and 394 as located above. Retained PDF
SHA256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
