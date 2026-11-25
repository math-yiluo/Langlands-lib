# Fraction-field tensors at a vertical point

`localizedGenericFibreFractionEquiv` identifies the base change of a
generic localization from \(B\) to \(Q\) with the fraction field of \(Q\),
when \(R \to Q\) is an injective local map of DVRs. Both rings localize
\(Q\) at the images of the nonzero elements of \(R\).

`tensorFractionFieldExtensionEquiv` identifies the generic fibre of an
injective local DVR extension \(R \to S\) with the fraction field \(E\)
of \(S\) over the fraction field \(K\) of \(R\). The isomorphism preserves
the \(K\)-algebra structure because the two maps from \(K\) agree on \(R\).
For a \(K\)-algebra \(L\), the resulting tensor comparison identifies
\(S \otimes_R L\) with \(L \otimes_K E\). It sends \(s \otimes x\) to
\(x \otimes \operatorname{algebraMap}(s)\).

These are derived localization and tensor comparisons used at the
generic points of the normalized closed fibre in Conrad's appendix to
Prasad–Yu, *On quasi-reductive group schemes*, author preprint,
Remark A.7 on printed and PDF p. 30. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
