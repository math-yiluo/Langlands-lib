# Traces on actual local module sections

This module constructs traces on sections of a finite free chart of a module
sheaf on an actual scheme. It is an internal linear algebra prerequisite for the
Lie trace criterion in Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90
(PDF p.98). That passage uses the trace of the actual endomorphism of the
relative Lie module. The present module constructs the section trace and its
compatibilities; it does not assert the arithmetic trace identity in that lemma.

The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
All results here are derived from the existing actual section, basis and sheaf
isomorphism constructions and Mathlib's trace of finite matrices.

Let \(X\) be a scheme, \(U\) an open, and \(M\) an \(\mathcal O_X\)-module
sheaf. Fix a finite type \(I\) and an actual trivialization
\[
e:\mathcal O_U^{(I)}\simeq M|_U.
\]
For a smaller open \(V\to U\), the existing `localSectionBasis e V` is an
actual basis of \(\Gamma(V,M)\) over \(\Gamma(V,\mathcal O_X)\). Given an
actual sheaf endomorphism \(f\) of \(M|_U\), `localSectionTrace e f V` is
the matrix trace of its induced linear map on these sections in that basis.
No field or reducedness hypothesis is imposed on the section rings.

`localSectionTrace_eq_trace` identifies this matrix trace with
`LinearMap.trace` of the actual section endomorphism.
`localSectionTrace_eq_basis` permits any other finite basis of that section
module. `localSectionTrace_trivialization_independent` consequently permits
any other finite sheaf chart, including a chart indexed by a different finite
type. These comparisons require the displayed finite chart; they do not
interpret Mathlib's trace on an arbitrary module without such a chart.

`localSectionTraceAddHom` is the additive map from actual sheaf
endomorphisms to structure-sheaf sections. Its evaluation is the constructed
trace. `localSectionTrace_one` computes the trace of the identity as the
natural-number image of \(|I|\) in the section ring. This is an equality in
that ring, without a nontriviality assumption or a claim that natural-number
images are injective.

For every arrow \(j:V\to W\) of smaller opens,
`localSectionTrace_restrict` proves
\[
\operatorname{res}_{W,V}(\operatorname{tr}_W(f))
=\operatorname{tr}_V(f).
\]
The proof expands the finite sum of diagonal entries and uses the existing
entrywise restriction theorem for the actual section matrices.

If \(h:M|_U\simeq N|_U\) is an actual sheaf isomorphism and
\(a\mathbin{\gg}h=h\mathbin{\gg}b\), `localSectionTrace_iso` gives equality
of the traces in the source chart and its transport through \(h\).
`localSectionTrace_iso_any_chart` permits any finite target chart.
The proof takes the trace of the already proved equality of transported
section matrices, then uses chart independence. It does not assume equality
of traces as extra data.

This local construction makes no global finite-freeness or chart-existence
claim and supplies no arbitrary-base-change theorem or moduli
representability result.
