# Actual finite quotient towers for triangular diagonal maps

This internal construction assembles the full triangular coordinate series into
an actual tower of affine group schemes. Its provenance is the previously
constructed coordinate series, quotient comparisons, character equivariance and
fpqc action descent. It invokes no additional external literature.

Work over any field `k : Type u`. Let `H` be affine and locally of finite type,
and let `j` map `H` into the upper triangular matrix group of size `N`. Let `D`
be an affine commutative group scheme locally of finite type, let `q : H → D`,
and let `d` map `D` to the diagonal Levi group. Assume that `q ≫ d` is the
original diagonal projection of `j`, that `q` is an fppf quotient by the full
kernel of that original projection, and that the composite representation of
`H` in the general linear group is a monomorphism on all test schemes.

The theorem `hasTower_of_affine_image_and_normal_quotient` proves
`LinearKernelTower.HasTower D (N * N) q` from these data and two additional
explicit premises: `AffineHomImageStatement` and
`AffineNormalSubgroupQuotientStatement`. Thus it is a conditional construction;
neither generic existence theorem nor a splitting theorem is proved here.
There is no algebraic closure, characteristic, smoothness or connectedness
restriction.

The definition `diagonalQuotientTerm` uses the supplied `D` and `q` as an actual
quotient of the first coordinate subgroup. The full first-term kernel identity
establishes the required quotient predicate. `seriesHom_le_first` proves
containment in that first term by induction. The helper
`QuotientTerm.comparison_isIso` identifies the canonical comparison between two
quotients by the same full subgroup with the previously constructed
`FppfQuotientComparison.iso`.

For positive `N`, the proof inducts on a natural number `t`, proving a tower of
length `t` for the canonical structural map from **any** supplied quotient by
the `t`-th series term to `D`. At zero, the same-kernel comparison is an
isomorphism. At a successor, normal quotient existence supplies the previous
quotient, and the comparison to it is fppf by its full actual kernel.
The factorization through its structural map follows after composing with the
original quotient map and applying fpqc homomorphism uniqueness.
`seriesComparison_isCharacterLinearKernel` supplies the actual character-linear
kernel, using generic affine-image existence and the original matrix
factorization. Repeated terms are covered by the zero coordinate and zero
character already present in that theorem. Flatness, surjectivity and
quasi-compactness of the structural map come from the quotient comparison and
the affine source and target.

At `t = N * N`, faithfulness makes the full series term trivial. The proof
chooses `H` itself with its identity homomorphism as the quotient by that
term. Its canonical structural map is exactly the supplied `q`, so no endpoint
transport of actions or kernel embeddings is needed. At `N = 0`, the first
full subgroup is already trivial, and the supplied fppf quotient is an
isomorphism by `IsFppfQuotient.isoOfBot`, giving the required length-zero tower.

Finally,
`admitsTower_diagonalizable_of_affine_image_and_normal_quotient` specializes to
`D(Λ)` for any finitely generated abelian character group in the original
universe, including groups with torsion. A closed triangular inclusion supplies
the faithful composite representation. The diagonalizable geometry instances
supply affineness and local finite type. This yields `AdmitsTower` for exactly
the supplied diagonalizable image map, for every `N` including zero. Closedness
of `d` is not required by this specialization. All subgroup identities and
monomorphisms refer to the full group-scheme functors, including nonreduced
test schemes; the proof does not replace them by rational-point groups.
