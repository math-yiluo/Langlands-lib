# Local boundedness and the compact-support pairing for Arthur truncation

`Langlands.Global.ArthurTruncation.truncationSelfAdjoint` proves
`Langlands.Global.ArthurTruncation.TruncationSelfAdjointStatement`.
For any compact Iwasawa subgroup in the statement, truncation preserves
left-rational-invariant measurable functions bounded on compact sets.
The constant term of the truncated function converges at every point
along each standard unipotent radical. With a continuous test function
of compact support modulo $G(F)$, both products in the sesquilinear
pairing are absolutely integrable and their integrals agree. The proof
works for every truncation parameter and uses $C=0$ for the threshold
in the target. [Exact statement](ArthurTruncationStatement.md)

## Sources

- J. Arthur, *An introduction to the trace formula*, in *Harmonic
  Analysis, the Trace Formula, and Shimura Varieties*, Clay Mathematics
  Proceedings 4 (2005), Chapter 1, §13, formula (13.1) and Proposition
  13.1(c), printed pp. 68–69, PDF pp. 80–81. The registered volume is
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- J. Arthur, *A trace formula for reductive groups I: terms associated to
  classes in $G(\mathbb Q)$*, Duke Mathematical Journal 45 (1978),
  §5, Lemma 5.1, printed pp. 936–937, PDF pp. 26–27. The registered
  source is `arthur-1978-trace-formula-reductive-groups-I`, SHA-256
  `80ec482ea894e3af960e79cc1316ac2c2e806ad466f92c106650a59a0b2f17cc`.
  The Lean proof uses the Library's qualitative cutoff finiteness
  theorem over number fields. [Finiteness proof](ArthurTruncationFinitenessProof.md)

Arthur writes the calculation on the norm-one quotient over
$\mathbb Q$. The target applies it on the full adelic quotient over a
number field and uses `rationalQuotientHaarMeasure` for the outer
integrals and `normalizedRationalQuotientHaarMeasure` for each radical
integral, as in the Library's truncation definition.

## Implemented proof

1. The parabolic cutoff is measurable, bounded by one and invariant
   under $P(F)$ and $N_P(\mathbb A_F)$. The height increment on a
   compact set enlarges the pointwise finite support to a uniformly
   finite set on that compact set. [Cutoff and support](ArthurTruncationCutoff.md)
2. The standard unipotent quotient is compact. The proof recognizes
   rational parabolic points in the standard subgroup functor and
   uses normality of the standard radical on both rational and adelic
   points. The normalized average of the input is measurable,
   locally bounded and $P(F)$-invariant. The finite support bound
   gives a locally bounded periodization, and the finite signed
   sum is locally bounded, measurable and $G(F)$-invariant. Its
   radical integrands are integrable by the compact-quotient bound.
   [Standard radical compactness](AdelicStandardConstantTermIntegral.md)
   [Measurable radical averaging](ArthurTruncationAverage.md)
3. The bilinear calculation unfolds each parabolic term on the
   rational parabolic quotient. Compact representatives of the
   original support and the radical quotient give integrability
   on both sides, and preservation of the integral under normalized
   radical averaging exchanges the factors. The finite signed sum
   gives the identity on the fundamental domain of $G(F)$. Pushing
   the restricted Haar measure forward gives the integrals on the
   specified rational quotient. Complex conjugation commutes with
   the radical integrals, the real cutoffs and signs, and both sums.
   Applying the bilinear result to the conjugate test function yields
   the stated pairing. [Parabolic pairing](ArthurTruncationParabolicPairing.md)
