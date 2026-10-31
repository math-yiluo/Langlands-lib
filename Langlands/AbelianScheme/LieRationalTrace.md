# Section traces of rational actions on actual relative Lie modules

This module applies the actual local-section trace construction to the
constructed rational action on the relative Lie module of an abelian scheme.
It is a derived prerequisite for Harris–Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90
(PDF p.98). Printed p.18 (PDF p.26) specifies the rational-isogeny convention
used by the existing rational Hom construction. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Fix an actual scheme \(S\), a commutative rational algebra \(R\), and an
actual map \(p:S\to\operatorname{Spec}R\). Let \(A/S\) be an abelian scheme
and \(\alpha:O\to\operatorname{End}^0(A)\) a unital ring map from a ring \(O\).
The target is the existing rationalization of the actual geometric Hom group.
The existing `lieRationalLocalOrderAction` and
`lieRationalSectionOrderAction` construct its actions on the relative Lie
sheaf and its sections. In particular, the endomorphism to be traced is
constructed from \(\alpha(a)\), rather than supplied as a separate linear map.

For an open \(U\), an actual finite trivialization
\(e:\mathcal O_U^{(I)}\simeq\operatorname{Lie}(A)|_U\), an element \(a\in O\),
and a smaller open \(V\to U\), `lieRationalSectionTrace p A α e a V`
is the trace of this rational action on the actual module
\(\Gamma(V,\operatorname{Lie}(A))\). It is a section of
\(\mathcal O_S(V)\), which may contain nilpotents.
`lieRationalSectionTrace_eq_trace` identifies it with Mathlib's intrinsic
linear-map trace, and
`lieRationalSectionTrace_trivialization_independent` proves equality for
any other finite Lie chart, with no requirement on its finite index type.

`lieRationalSectionTraceAddHom` bundles the trace as an additive map
\(O\to\mathcal O_S(V)\); its evaluation theorem identifies it with the
constructed trace. `lieRationalSectionTrace_one` gives
\[
\operatorname{tr}(\alpha(1)\mid\Gamma(V,\operatorname{Lie}(A)))
=|I|\quad\text{in }\mathcal O_S(V).
\]
This computes a section-ring value, without asserting injectivity of the
natural-number map.
`lieRationalSectionTrace_restrict` proves compatibility with every actual
smaller-open restriction of both the Lie sections and the structure sheaf.

Finally, let \(e:A\simeq B\) be an isomorphism in the actual rationalized
abelian-scheme category. Thus it includes an actual rational inverse.
Suppose it intertwines \(\alpha\) and \(\beta\) in the existing `comp0`
convention. `lieRationalSectionTrace_iso` proves
\[
\operatorname{tr}(\alpha(a))=\operatorname{tr}(\beta(a))
\]
on each smaller open and in arbitrary finite charts for the two relative Lie
sheaves over the same open. The proof uses the already constructed
`lieLocalIso0`, its proved intertwining equation, and equality of local-section
traces under actual sheaf isomorphisms. No equality of traces or comparison
isomorphism is assumed independently of the geometric rational isomorphism.

This contribution constructs the trace operation and proves its intrinsic
compatibilities. It does not impose or prove the arithmetic equality in
Lemma III.1.2(3), its equivalence with Harris–Taylor's original
\(\operatorname{Lie}^+\) compatibility, the prescribed relative dimension,
arbitrary-base-change naturality, or representability of the PEL functor.
It does not assert the existence of a finite chart. These remain separate
conditions or construction obligations of the Harris specialization.
