# Finiteness of normalization over a complete DVR

The definition `normalizationToComponents` maps the integral closure
in total fractions to the product of the integral closures of the
minimal-prime quotients in their fraction fields. Non-zero-divisors
remain nonzero in every minimal-prime quotient, which defines the
map on fractions. Images of integral fractions are integral over
the respective quotients. For a reduced ring the map is injective,
since the numerator of a fraction that maps to zero belongs to
every minimal prime. In the Noetherian case there are finitely
many components, so module finiteness of the component
normalizations implies module finiteness of the original one.

For a finite-type domain with an injective structure map from a
complete DVR with perfect residue field, the proof tests finiteness
on opens around maximal ideals. In the closed fibre it lifts a
polynomial chart and uses the quasi-finite form of Zariski's main
theorem to find a finite chart after localization. Finite Frobenius
on the base passes to the polynomial ring by finite type and
integrality. An iterate of Frobenius embeds the integral closure
in a finite field extension into the integral closure in the
separable subextension, which is finite by the trace argument.
This extends the Library's argument for finite-type integer algebras.

For a maximal ideal in the generic fibre, the proof inverts the
uniformizer. Frobenius remains finite on the fraction field since
every nonzero denominator divides its Frobenius image. The affine
Noether normalization over that field gives a finite polynomial
chart. The local module finiteness tests imply global finiteness.

For a flat finite-type algebra with smooth generic fibre, flatness
and smoothness give reducedness of the original algebra and ensure
that the base maps injectively into each minimal-prime quotient.
The component argument proves finite normalization in total
fractions. The comparison with integral closure in the generic
fibre then gives `finite_integralClosure_genericFibre_of_completeDvr`.

This is an affine finiteness step in the complete-base setting of
Conrad's appendix to Prasad–Yu, *On quasi-reductive group schemes*,
author preprint, Theorem A.6 (p. 30). The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
