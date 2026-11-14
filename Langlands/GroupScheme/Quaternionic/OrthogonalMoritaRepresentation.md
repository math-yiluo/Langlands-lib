# A Morita comparison retaining the actual row representation

This module defines an interface for comparing a division-algebra isometry
group with the explicit split even orthogonal group. It does not assert that
the interface is inhabited.

Let `K` be a field, `D` a finite-dimensional division `K`-algebra, `σ` a
first-kind involution, and `q` a `σ`-quadratic form on `D^m`. Let `L/K` be a
field extension. An `OrthogonalMoritaComparison σ q L degree n` consists of:

- An actual group-scheme isomorphism over `L` from the base change of `O(q)`
  to `OrthogonalMatrix.groupScheme (Fin n)`, the split orthogonal group on
  `L^(Fin n ⊕ Fin n)`.
- An `L`-linear equivalence from `L ⊗[K] D^m` to `degree` copies of that
  `2n`-dimensional row module.
- Compatibility of these identifications with the actual actions over
  every commutative coefficient `L`-algebra `R`, with its compatible
  `K`-algebra structure. The source is the published inverse-right row
  action transported to `R ⊗[K] D^m`. The target is right multiplication
  by the inverse of the matrix of the corresponding orthogonal point,
  separately in each of the `degree` copies.

The coefficient comparison is fixed by the single equivalence over `L`.
`OrthogonalMorita.rowEquivOver` extends it using tensor associativity and
cancellation, finite-product distribution, and the tensor unit equivalence.
Thus it introduces no independent choice for different coefficient algebras.
`rowEquivOver_tmul` computes its value on `r ⊗ v`: the `(j,x)` entry is
the image in `R` of the `(j,x)` entry of the original comparison at
`1 ⊗ v`, multiplied by `r`. Tensor induction and compatibility of an
algebra map with `L` then prove `rowEquivOver_naturality`.

`FirstKindInvolution.isometryTensorRowAction` conjugates the published
`isometryRowActionOver` by the finite-product tensor equivalence.
`piRight_isometryTensorRowAction` records this identity on rows.
`OrthogonalMorita.splitPoint` uses the published pullback-adjunction
comparison `affinePointsBaseChangeMulEquiv`, followed by the actual
group-scheme isomorphism, to compare coefficient points. The matrix in the
compatibility condition comes from the published inclusion of the split
orthogonal group into its general linear group.

This is derived internal interface design. It combines the existing
division-algebra row action, actual base-change point comparison, and split
orthogonal model without adding a literature assertion. Its definition
imposes no centrality, degree, nondegeneracy, algebraic-closedness, infinitude,
or characteristic hypothesis. An existence statement needs appropriate
additional hypotheses. The interface retains the row representation that
an abstract isomorphism of group schemes alone would not specify.
