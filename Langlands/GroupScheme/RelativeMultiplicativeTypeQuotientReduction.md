# Reduction of multiplicative-type quotients to affine diagonalizable kernels

Internal derived reduction toward affine quotients by central
multiplicative-type subgroups over arbitrary bases
(`RelativeCentralMultiplicativeTypeQuotientStatement`).

`AffineDiagonalizableNormalQuotientStatement` asks for an affine fppf quotient
of an affine group over an affine base by a closed normal diagonalizable
subgroup. The character group in diagonalizability is finitely generated,
as in the published definition. This proposition is an explicit premise in
the reduction theorems; the module does not prove it.

On an affine base, choose an fppf cover that diagonalizes the kernel. Flat
maps locally of finite presentation are open, so the cover is quasi-compact.
The finite affine refinement theorem then supplies finitely many affine
members. Their disjoint union is affine and maps faithfully flat and
quasi-compactly to the base. Each component inherits diagonalizability via
the actual base-change comparison isomorphisms. Apply the supplied affine
diagonalizable construction to the iterated base changes, glue the quotients
on the disjoint union, and apply effective affine fpqc quotient descent.

Over an arbitrary base, apply this result on the affine open cover and use
open gluing for arbitrary represented kernels. The last theorem applies the
normality of central subgroup functors and implies the published central
multiplicative-type quotient target, conditionally on the displayed affine
diagonalizable premise. Smoothness and connected geometric fibres are not
needed by this conditional reduction.

All content is derived from the cited-by-import Library and Mathlib
constructions, with no new literature assertion. Open gluing and effective
descent retain the full kernel on all scheme tests.
