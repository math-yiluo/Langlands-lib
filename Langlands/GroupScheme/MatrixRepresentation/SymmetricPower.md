# Actual finite symmetric powers of matrix representations

For an actual matrix representation `rho` of any group scheme over `Spec R`,
where `R` is an arbitrary commutative ring, `rho.symmetricPower d` is an
actual matrix representation on `Index n d`, the finite set of degree-`d`
monomials in the original finite coordinate type `n`. No affineness,
finite-type, smoothness, reducedness or characteristic assumption is imposed
on the group or base ring.

For every scheme test `T`, take `rho.pointMatrix T x`, apply the canonical
symmetric general-linear homomorphism from the companion algebra module,
and translate back to an actual general-linear point. The symmetric matrices
preserve multiplication, so this is a homomorphism of test-point groups.
Their coefficient-ring naturality and the naturality of the original
representation prove compatibility with arbitrary pullbacks of test schemes.
The existing `homOfPoints` constructor therefore gives an actual group-scheme
morphism into the finite general linear group.

`symmetricPower_pointMatrix` gives exactly this formula on every scheme test.
`symmetricPower_affineMatrix` gives it directly in each affine test algebra,
using its canonical global-section isomorphism. In particular all nonreduced
affine algebras remain included. `symmetricPower_restrict` proves compatibility
with restriction along any group-scheme homomorphism by equality on all tests.

This internally derives the coordinate construction of the symmetric action
used in the source's Nagata proof. The polynomial generators represent the
original free module's basis vectors, with the matrix-column convention
specified in the companion Markdown. No assertion about the Frobenius
subspace's stability, linear reductivity, or the existence of a splitting
is made in this module; those are subsequent proof obligations.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, proof of Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
