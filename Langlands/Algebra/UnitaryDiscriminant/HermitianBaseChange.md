# Norm criterion after a Hermitian scalar extension

Let \(A\) be a degree-\(2m\) central simple algebra with unitary involution
over a quadratic field center \(L/F\). Supply a finite Galois extension
\(M/F\) containing \(L\) and a matrix splitting chart for \(A\) over \(M\).
Let \(F'/F\) be a scalar extension with \(F'\) of characteristic zero.
The extended pair on \(L'\otimes_L A\) has quadratic Galois field center
\(L'/F'\) and a matrix chart in which its involution is adjoint to an
invertible Hermitian Gram matrix \(H\). The nontrivial center automorphisms
intertwine on \(L\), and the involutions agree on \(1\otimes A\).
`scalarExtension_discriminantClass_eq_zero_iff_norm` identifies vanishing
of the scalar-extended discriminant Brauer class defined by the original
chart with the condition that \(d\in F'^\times\) is a norm from \(L'\),
where \(d\) maps to the signed Gram determinant \((-1)^m\det H\). The fields
and algebra share a universe.

The proof embeds the original splitting field and the new center into
the algebraic closure of \(F'\), using compatible embeddings over the
old center. It takes a single finite Galois stage containing both images.
Base change and the Hermitian matrix calculation identify the relative
class there with the carry class for the inverse signed determinant.
The character is the inflation of the quadratic character of
\(L'/F'\). Injectivity of relative and continuous inflation reduces
vanishing to the quadratic carry class over \(L'\), which vanishes
precisely on norms. The norm subgroup is closed under inversion.
