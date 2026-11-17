# Extensions of groups of multiplicative type over a field

Workers 312 and 603. Proof of the unchanged published proposition
`Langlands.GroupScheme.MultiplicativeTypeFieldExtensionStatement.{u}`.

The final theorem `multiplicativeTypeFieldExtension` covers every field and
universe, including finite nonsmooth multiplicative-type groups and torsion
character groups. It adds no hypotheses to the published target.

For the commutative case, base change to the algebraic closure of the original
field. The published multiplicative-type splitting lemmas make both outer groups
diagonalizable there. The monomorphism identifies the kernel as a closed
subgroup, and the quotient remains fppf after base change. Affine descent and
finite presentation of that projection make the middle group affine of finite
type. Commutativity survives base change.

Translate this sequence to maps of actual coordinate Hopf algebras. The
surjective map to the kernel's group algebra grades the middle coordinate
algebra by the kernel's character group. The degree-zero part comes from the
quotient's group algebra, so it is spanned by group-like elements. Commutativity
of the middle group makes its coordinate coalgebra cocommutative. Over the
algebraically closed field, the graded group-like spanning theorem then spans
the entire coordinate algebra by group-like elements. Its proof uses a common
eigenvector of the commuting translation operators in each nonzero grade, and
multiplication by that invertible group-like element reduces the grade to zero.

Group-algebra reconstruction gives a diagonalizable presentation. The coordinate
algebra is finite type; transport through this reconstruction and the group
algebra finite-type criterion make the group of group-like elements finitely
generated. This gives the diagonalizable model over the chosen algebraic closure
required by `IsMultiplicativeType`.

For a connected quotient, Worker 603's connected-quotient theorem makes the
middle group commutative without smoothness assumptions. Apply the preceding
commutative case. For the second clause, Worker 603's central diagonalizable
extension theorem takes the first clause for this exact sequence. A split torus
quotient is connected, so the middle group is multiplicative type and therefore
commutative. The Hopf-algebra argument for central extensions with split-torus
quotient supplies a diagonalizable model over the original field.

These are internal combinations of the cited Library interfaces and same-task
supporting modules. The proof route replaces the source's commutative
characterization and Galois-twist arguments by the implemented graded Hopf-algebra
constructions. The source correspondence is recorded in the unchanged target
Markdown; no independent source claim is added here.
