# Actual Hecke test functions and subgroup invariance

This module uses `Langlands.HarmonicAnalysis.SchwartzBruhat X`, the existing
complex vector space of locally constant compactly supported functions, and
its existing local-constancy, compact-support and continuity lemmas directly.
The constructions below are in the `Langlands.Hecke.TestFunction` namespace.
The functions have their actual values on `X`; no additional carrier is introduced.

For any topological space, the module provides the faithful inclusion into
compactly supported continuous maps, proves that support is clopen and equals
topological support, and proves compactness of the support and each nonzero
fiber. Pullback along an actual homeomorphism is a complex linear equivalence,
with inverse pullback along the inverse homeomorphism. The indicator of an
actual compact clopen set is a test function, with support exactly that set.

For a topological group, `leftTranslate g` sends `f(x)` to `f(g⁻¹x)`,
and `rightTranslate g` sends it to `f(xg)`. The module proves their identity,
composition and commutation laws directly on values. Inversion sends `f(x)`
to `f(x⁻¹)` and is an involutive linear equivalence. This inversion does not
include conjugation or a modular factor and is not asserted to be a
convolution star operation.

`biInvariant K L` is the actual submodule of functions invariant under left
translation by `K` and right translation by `L`. Membership is equivalent
to being fixed by both translation operators. Smaller subgroups give larger
subspaces; inversion exchanges the two subgroups. The characteristic function
of a supplied compact open subgroup belongs to its bi-invariant subspace.
It is unnormalized; Haar normalization, convolution and the corner-algebra
identification remain separate constructions.

These are intrinsic constructions on the test functions recalled in Flath,
*Decomposition of representations into tensor products* (1979), printed p.179,
PDF p.175 of the Corvallis Part I volume, registered as
`flath-1979-tensor-products`. Flath defines the Hecke algebra by convolution
on this space, and uses the normalized subgroup indicator in its corner.
The present module supplies the function and invariance prerequisites.
Its proofs use pullback and compact-support preservation under homeomorphisms,
clopen fibers of locally constant functions, and subgroup cancellation.
No Haar measure, convolution law, action on arbitrary representations, spherical
commutativity, Satake parameter or factorization theorem is assumed or proved.
