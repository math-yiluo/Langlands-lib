# Complex-linear comparison of Galois-related matrix charts

This internal construction starts with the actual factor equivalence in
`GaloisMatrixFactors`. It retains all of that module's number-field,
algebra, involution, Harris signature-chart, compatible CM-section and
finite-basis inputs. Write `F_(s,i)` for `embeddingFactorGaloisEquiv hΦ b s i`,
where `s` is a rational algebra automorphism of the complex numbers and
`i : K →+* ℂ`. Write `S_s` for entrywise application of `s` to a square
complex matrix, implemented by Mathlib's `RingEquiv.mapMatrix`.

`embeddingChartComparison hΦ b s i` constructs

\[
  E_{s,i}=F_{s,i}\circ S_{s^{-1}}
    : M_n(\mathbf C)\simeq_{\mathbf C}M_n(\mathbf C).
\]

The order of composition is part of the definition: the inverse coefficient
map acts first. The underlying map is a ring equivalence, since both factors
are ring equivalences. To promote it to a complex algebra equivalence, the
proof writes each scalar matrix as `z • 1`. The lemma
`ComplexMatrix.mapMatrix_smul` proves entrywise semilinearity directly from
`s(z M_rc) = s(z) s(M_rc)`. Semilinearity of `F_(s,i)` then cancels the inverse
scalar twist, while both ring maps preserve the unit. Thus the constructed
comparison fixes every complex scalar matrix; no complex-linearity or
chart-comparison hypothesis is supplied.

`embeddingChartComparison_apply` exposes the defining composite.
`embeddingChartComparison_map` proves

\[
  E_{s,i}(S_s(M))=F_{s,i}(M).
\]

Its proof cancels `s⁻¹(s(M_rc))` entry by entry. Applying the existing factor
evaluation identity gives `embeddingChartComparison_evaluation`:

\[
 E_{s,i}\bigl(S_s(\operatorname{ev}_i(a))\bigr)
   =\operatorname{ev}_{s\circ i}(a)\qquad (a\in A).
\]

Finally, `embeddingMatrixGaloisEquiv_chartComparison` combines this cancellation
with the factor-dependence theorem to express the full matrix action `T_s` as

\[
  T_s(x)(s\circ i)=E_{s,i}(S_s(x(i))).
\]

The provenance is the constructed factor equivalence and Mathlib's entrywise
ring equivalence, with the scalar and cancellation proofs above. The generic
entrywise lemma applies also when `n = 0`; the Harris specialization retains
the rank condition already required by the signature-chart data. This unit
does not construct a conjugating matrix for `E_(s,i)`. Matrix-automorphism
innerness and the scheme-cocharacter reflex comparison remain subsequent
steps.
