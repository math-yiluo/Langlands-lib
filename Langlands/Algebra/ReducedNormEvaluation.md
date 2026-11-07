# Evaluation of the descended determinant polynomial

This internal construction takes a finite basis `b : Basis J K A` and an actual
matrix chart `e : L tensor_K A ≃ Matrix I I L` over a finite Galois field
extension. The matrix index is finite and nonempty. It constructs the norm on
every commutative `K`-algebra, without a reducedness, nontriviality or
injectivity assumption on that scalar algebra. The coefficient field, algebra,
indices and test algebras have independent universe parameters.

`polynomialValue b P R x` evaluates the actual polynomial `P` at the
coordinates of `x` in the scalar-extended basis `b.baseChange R`.
`sum_coordinates_tmul` expresses `x` as the finite sum of those coordinates
tensored with the original basis vectors. `coordinates_naturality` proves
that arbitrary scalar-algebra maps carry these coordinates to the coordinates
of the scalar-extended tensor. Its proof uses tensor induction and the
pure-tensor coordinate formula. `polynomialValue_naturality` then follows
from the ring-homomorphism compatibility of polynomial evaluation.

For a commutative algebra `R` over `L`, with its compatible `K`-algebra
structure, `splittingMap e R` extends the map on `a : A` given by the
coefficientwise scalar extension of `e(1 tensor a)`. The tensor universal
property makes this an actual `R`-algebra homomorphism on `R tensor_K A`.
`descendedPolynomial_eval_det` proves that evaluation of the descended
polynomial equals its determinant: first extend the polynomial coefficients
from `K` to `L`, apply the defining descent identity, and evaluate the
generic determinant. The finite coordinate expansion identifies the resulting
matrix sum with `splittingMap e R x`. This proves the comparison on every
commutative `L`-algebra, including nonreduced ones.

`normFromGalois b e R` is this coordinate evaluation as a multiplicative map
with zero. Its zero, one and multiplication laws are proved by mapping `R`
into `L tensor_K R` through the right tensor factor. That map is injective:
`R` is flat over the field `K`, and the field map `K → L` is injective.
Naturality and the determinant comparison turn each proposed identity into
the corresponding determinant identity there, and injectivity reflects it
back to `R`. The same comparison proves the scalar formula
`N(r tensor 1) = r ^ card I` and independence of the coordinate basis, allowing
different finite indexing types.

The polynomial is homogeneous of degree `card I` by the preceding descent
helper. Its nonvanishing follows by evaluation at the identity tensor, whose
norm is one in `K`. `descendedPolynomial_basis_totalDegree` therefore proves
that its total degree is exactly `card I`. These are facts about the actual
coordinate polynomial, not just its field-valued function.

`normFromGaloisUnits` applies `Units.map` to the constructed multiplicative
map. `normFromGaloisOne` is its actual group kernel. The membership theorem
identifies membership with norm one on the underlying unit value, and the
last theorem proves naturality of the group homomorphisms.

The source convention is Milne, *Algebraic Groups* (2022 corrected reprint),
Remark 24.25, printed p. 523 / PDF p. 534, registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The retained author errata of 2026-11-04 do not correct this passage. The
all-test coordinate evaluation and faithful comparison argument here are an
internal derivation of that determinant convention. This helper still takes
the finite Galois splitting chart as input. Construction of such a chart,
independence across different splitting fields and the unconditional
central-simple-algebra interface remain separate units.
