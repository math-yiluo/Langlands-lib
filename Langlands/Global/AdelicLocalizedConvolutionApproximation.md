# Approximate identities supported over finite adelic subgroups

`Langlands.Global.AdelicGroupPoints.HasFiniteProjectionSupport L h`
means that each nonzero value of \(h\) is at an adelic point whose
finite projection belongs to \(L\).

`exists_rightConvolution_approximation_in_nhds` simultaneously
approximates finitely many continuous functions on a compact set
using a smooth test kernel supported in a prescribed neighborhood
of the identity. Continuity and the compact set give a common
translation neighborhood on which all the errors are small. The
nonnegative kernel of mass one is chosen in its intersection with
the prescribed neighborhood. Integration bounds the convolution
error by the same tolerance.

`exists_averaged_rightConvolution_approximation_of_finite_support`
uses the inverse image of an open finite adelic subgroup as the
prescribed neighborhood. Given two fixed reproducing weights on
an infinite compact, the right averaging leaves the convolution
on the supplied family unchanged. Left averaging transfers the
uniform bound by the integral of the absolute value of the left
weight. The proof chooses the unaveraged tolerance small enough
to absorb that integral.

`hasFiniteProjectionSupport_averaged` uses that infinite
translations do not change the finite coordinate. The same
support condition holds for all positive convolution powers,
since if \(y\) and \(y^{-1}x\) project into a subgroup, then so does
\(x\).

The construction localizes the two-sided compact averaging
of an approximate identity in Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series*, I.4.5, printed pp. 60–61
(`moeglin-waldspurger-1995-spectral-decomposition`, collection
fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
This restriction supplies kernels for the finite-compact transport
of the convolution equation in `AdelicHarishChandraFiniteCompactChange`.
