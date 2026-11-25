# No nonzero nilpotent tangent matrices for linearly reductive groups

For a field `k` of nonzero characteristic `p`, assume exactly the following
linear-reductivity condition: every actual matrix representation on `Fin d`
is semisimple in the published all-affine-test stable-subspace sense.
`tangentMatrix_eq_zero_of_isNilpotent_of_linearlyReductive` proves that
any nilpotent tangent matrix in any finite-coordinate representation is zero.
The tangent vector is an actual dual-number kernel point of the group.
There is no affineness, finite-type, smoothness, reducedness, perfectness,
algebraic-closure or faithfulness hypothesis on the group or representation.

`IsFrobeniusSplittable rho p` means that the actual symmetric power has an
all-affine-test equivariant projection onto its actual Frobenius subspace.
Reindexing to `Fin d` lets the exact reductivity hypothesis imply
semisimplicity of the finite monomial symmetric representation. Its stable
Frobenius range then has such a projection.
`IsFrobeniusSplittable.restrict` preserves the same projection along every
group-scheme morphism, using the actual restriction formula for symmetric
powers. This is the restriction assertion used here; no inheritance of
linear reductivity by arbitrary closed subgroups is asserted.

The algebraic obstruction is implemented in the polynomial coordinates
of the actual symmetric representation. `linearForm` embeds the original
coordinate vector space into linear polynomials; its linear coefficients
prove injectivity. The genuine polynomial derivation of a matrix acts on
these linear forms by the original matrix. A nonzero nilpotent matrix,
viewed as an endomorphism through the matrix/linear-map equivalence, has
a chain `N x = y`, `N y = 0`, with `y` nonzero.

In degree `p`, let `z = linearForm(y)^(p-1) * linearForm(x)` and
`w = linearForm(y)^p`. Both are actual homogeneous polynomials. The
symmetric differential sends the coordinate vector of `z` to that of
`w`. The vector of `w` belongs to the pure-power inclusion range by the
characteristic-power sum formula; this uses no extraction of `p`th roots
in `k`. It is nonzero because the linear-form embedding is injective and
the polynomial algebra over a field is a domain. The differential kills
the whole pure-power range, since every derivation in characteristic `p`
kills `p`th powers.

If a projection onto that range commuted with the symmetric differential,
it would fix `w` and its value on the differential of `z` would also be
zero. `SymmetricDifferential.not_isProj_of_isNilpotent` gives this
contradiction. For an actual equivariant projection, the published
intertwiner differentiation theorem supplies commutation with the actual
symmetric tangent matrix. `symmetricPower_tangentMatrix` identifies that
matrix with the genuine derivation matrix just computed. This proves
`tangentMatrix_eq_zero_of_isNilpotent_of_isFrobeniusSplittable`, and the
linear-reductivity splitting gives the final theorem. Primality and
positivity of `p` are derived from its nonzero field characteristic.

This internally derives the infinitesimal symmetric-power obstruction in
the source, which applies it to a faithful representation of alpha_p.
The implemented theorem records the more general consequence for every
nilpotent actual tangent matrix. The classification of connected groups
and the conversion to the full identity-component conclusion of Nagata's
theorem remain separate obligations; this module does not prove that theorem.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, proof of Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
