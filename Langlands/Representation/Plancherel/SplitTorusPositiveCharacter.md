# Positive smooth characters on actual split tori

This internal companion constructs the positive character of a real parameter
using the existing positive valuation and the actual real torus pairing. Its
value at an actual point is `exp(-pair(parameter, valuation(point)) * log q)`,
viewed as a complex unit. The character takes positive real values, satisfies
the required `q^(-pair)` norm formula, and has open kernel for the canonical
rational-point topology. The proof of openness uses the published openness of
the actual common norm kernel, which it contains. The topology theorem
uses the standard affine-scheme instance needed to form
`rationalPointTopology`; splitness already implies this instance via
`IsSplitTorus.isAffineHom`. Its proof derives finite type from the published
smoothness of split tori, so no extra finite-type hypothesis is imposed.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 version, V.2.3 and V.2.5 (printed pp.105–107/PDF pp.111–113), and
V.3.19–V.3.20 (printed pp.115–116/PDF pp.121–122), registered as
`renard-2026-representations-groupes-reductifs-padiques`. This implementation
uses the positive valuation convention in V.2.3 and the exponential
`s ↦ q^(-s)` convention of V.3.20. The separately named raw logarithm differs
by the exact scalar `-log q`.

The section valuation lemma consumes the shared intrinsic uniformizer
evaluation theorem. Evaluation on pure tensors then proves that the normalized
real part of the positive character is precisely the supplied parameter.
This is a construction law, with no real-part existence or norm-formula
hypothesis. The additive, zero, and negation laws follow from the real
exponential identities. All fields and actual tori retain arbitrary universe,
both characteristics and rank zero.
