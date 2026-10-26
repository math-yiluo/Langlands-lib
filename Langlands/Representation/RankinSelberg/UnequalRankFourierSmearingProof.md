# Global and pointwise JPSS Fourier smearing

`Langlands.RankinSelberg.unequalRankFourierSmearingStatement` proves
`Langlands.RankinSelberg.UnequalRankFourierSmearingStatement.{uF,uV} F T n j k`,
for every prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural `n,j,k`. The field and representation
universes are independent. The published statement and its imported
Lean/Markdown pairs are preserved.

Worker 582 implemented the matrix calculation and final proof. The two
finite algebraic averaging lemmas in the companion
`UnequalRankSmearingAverage` module are extracted from Worker 180's
unreviewed adjacent-span draft revision 10, retaining their names in
`Langlands.RankinSelberg.Smearing`. They are included with this proof for
independent review, with Worker 180 credited as a coauthor.

## Implemented proof

Install the topology, valuative relation, local-field structure and Borel
measurable space of the supplied `T`. The published `T.fieldT2`,
`T.secondCountableTopology` and `T.sigmaCompactSpace` results, imported
through `PadicScalarHaarScalingProof`, supply the separation, countability
and sigma-compactness facts needed for the product row measure. In
particular, the supplied scalar additive Haar measure is sigma finite,
and `rowMeasure ν (n+1)` is finite on compact sets. These structures all
refer to this `T`.

Write `U(z) = unequalRankSmearingUnipotent n j k z`.
Its published continuity theorem lets
`Smearing.exists_coefficient_average` produce one coefficient `f₁` in
the original `coefficientModel π ℓ`. For every element `h` of the whole
large general linear group, it proves both

`Integrable (fun z => κ z * f(h * U(z))) (rowMeasure ν (n+1))`

and

`f₁(h) = ∫ z, κ z * f(h * U(z)) ∂rowMeasure ν (n+1)`.

Nested subtype values are omitted in these displayed formulas.
The averaging lemma takes a preimage of `f` under the coefficient map.
Smoothness makes its orbit locally constant. Multiplication by the
Schwartz–Bruhat weight gives compact support, so the published
simple-function and algebraic-integral APIs construct a finite sum of
vectors in the original representation carrier. Applying an algebraic
linear functional to that sum commutes with the integral. Testing with
the Whittaker functional composed with `π(h)` proves the integrability
and formula for every `h`. No topology or completeness on the carrier is
needed. The explicit integrability assertion prevents reliance on the
value assigned to a nonintegrable Bochner integral.

Keep this same `f₁` and evaluate its formula at
`B = unequalRankMatrix (j+1) k g X`. The companion theorem
`unequalRankMatrix_smearing_coefficient` proves, using the actual
upper-unipotent conjugate and standard character,

`f(B * U(z)) = ψ.complex (rowPairing z (X (Fin.last j))) * f(B)`.

Its entrywise matrix proof is described in
[UnequalRankSmearingConjugation.md](UnequalRankSmearingConjugation.md).
Substitute this identity into the integral, commute the complex scalar
factors, and use `integral_mul_const` to obtain

`f₁(B) = rowFourierIntegral ψ ν (n+1) κ (X (Fin.last j)) * f(B)`.

The supplied `IsRowFourierPair ψ ν κ Φ` premise identifies that Fourier
integral with `Φ (X (Fin.last j))`. This proves the pointwise cutoff for
the very coefficient already satisfying the global formula.

## Original formulas and conventions

The original sources, including their displayed matrices and Fourier
formulas, were read directly:

- Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
  Amer. J. Math. 105 (1983), 367–464, registered as
  `jpss-1983-rankin-selberg`, printed pp.394–395, the lemma inside the
  proof of Theorem 2.7 and its use in §2.8 (retained PDF pages 29–30).
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- The same authors, *Automorphic Forms on GL(3) I*, Ann. of Math. (2)
  109 (1979), 169–212, registered as `jps-1979-gl3-i`,
  Proposition 4.1.4 and Lemma 4.1.5, printed pp.188–190
  (retained PDF pages 21–23). In particular, p.189 computes
  the conjugate and its character, and p.190 states that the average
  remains in the Whittaker model.
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

No source-specific errata note was found in the supplied project notes or
literature. In the 1983 displays the source's leading rank is `t=n+1`,
its middle size is `j_source=j+1`, and its full rank is
`r_source=n+((j+1)+k+1)+1`. The block matrix has trailing size `k+1`;
the smearing matrix splits its first trailing coordinate from a final
identity block of size `k`. The character calculation pairs the last
rectangular row with the leading smearing column.

The source defines the global average using the reflected transform
`Φ̂(-z)` and states a last-row integrated identity. The 1979 proof
explicitly computes the conjugate's character with a plus sign.
Here `κ` is supplied with precisely the premise

`Φ(y) = ∫ z, ψ.complex (∑ i, z i * y i) * κ(z) ∂rowMeasure ν (n+1)`.

Consequently the proof needs neither inversion nor a choice of
self-dual Haar measure. The arbitrary supplied Haar measure, independent
universes, and merely smooth coefficient-image representation are derived
extensions already specified by the published target. The finite
algebraic averaging construction supplies their proof; these exact
interfaces are not asserted to occur verbatim in the papers.

There are no irreducibility, nonzero-functional, Fourier-surjectivity or
extra conjugation hypotheses. The result proves no quotient-integral,
analytic-continuation or row-integrated consequence. Such consumers must
supply their own convergence and interchange arguments.
