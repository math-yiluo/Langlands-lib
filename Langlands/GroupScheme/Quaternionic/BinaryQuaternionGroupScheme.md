# Actual binary quaternion product morphism

Authors: Worker 124.

This internal unit constructs the actual morphism from
`SL₂ × SL₁(D)` to the published isometry group of the quaternionic
hyperbolic plane. It starts from the coefficient-group action in
`BinaryQuaternionAction`; no classification, simple connectedness or
central-isogeny comparison is assumed.

`groupScheme` is the categorical product of the actual binary
special-linear group scheme and the actual reduced-norm-one group.
`pointsEquiv` identifies its points on every relative test scheme `T`
with `SL₂(R) × reducedNormOne(K,D,R)`, where `R` is the actual relative
global-section algebra. The constructed `tensorMatrixEquiv` commutes
extension of scalars with binary matrices over every commutative
coefficient ring. It is built from the existing matrix/tensor and tensor
associativity algebra equivalences. Its pure-tensor formula, naturality
and adjoint compatibility are proved in this module. This extends the
same formula used by `BinaryElementary.Splitting.tensorMatrixEquiv` in
`Langlands.Algebra.BinarySplittingNorm`, whose coefficient parameter is
a field; no field assumption is imposed here on the coefficient ring.

Combining these comparisons with the concrete action gives `pointMatrix`.
The all-test naturality laws for special-linear points and norm-one
points, together with coefficient naturality of the concrete action,
prove `pointMatrix_naturality`. The inverse matrix-unit point comparison
gives `unitPoints`, and its naturality constructs `unitHom`, an actual
homomorphism into the actual unit group scheme of `M₂(D)`. The theorem
`unitHom_points` states its tensor matrix on every relative test.

`unitHom_kernel` transfers the concrete exact kernel equation to this
morphism. A kernel point has coordinates `(rI,scalar(r))`, with `r*r = 1`
in the section algebra. These coordinates commute with every product
point after every further test restriction. Thus
`unitHom_kernel_isCentral` proves centrality of the full represented
kernel, including any non-smooth part, rather than only centrality of
field-valued points.

`hyperbolicForm σ` is the class of `[0,1;0,0]` in the published quotient
`σ.QuadraticForms (Fin 2)`. Over an infinite ground field, the actual
coefficient action preserves this class. Adjoint compatibility of the
matrix/tensor equivalence and the published equality between the
base-changed alternating subspace and the alternating subspace of the
extended involution transport this preservation to the defining defect
condition of the published `σ.isometryGroup`. Consequently
`unitHom_range_le_isometry` proves range containment on every test.
Factoring through that represented closed subgroup constructs
`isometryHom`. Its composite with the original isometry inclusion is
`unitHom`, and `isometryHom_points` records the concrete formula.
Monicity of the inclusion transfers the exact all-test kernel equation
and centrality to `isometryHom_kernel` and
`isometryHom_kernel_isCentral`.

The characteristic is unrestricted, and the coefficient tests may be
nonreduced. The infinite-field hypothesis is used only for the
hyperbolic-isometry factorization, through the earlier conjugation norm
identity. The unit does not yet prove that the product source is simply
connected, that the isometry morphism is a central isogeny onto the
identity component, or that it compares with the kernel or Levi
preimage in an arbitrary larger spin cover. Elementary generation and
the host Kneser–Tits theorem remain open.
