# Group-like bases from orthogonal idempotents in the convolution dual

Let \(R\) be a commutative ring and let \(C\) be an \(R\)-coalgebra whose
underlying module is finite free. Its convolution dual is the actual algebra
\(D=\operatorname{Hom}_R(C,R)\), represented in Lean with `WithConv`.
Neither cocommutativity of the coalgebra nor commutativity of its convolution
algebra is assumed.

## Primal coordinates

`primalBasis b` takes a finitely indexed \(R\)-basis \(b\) of \(D\) and
returns an \(R\)-basis \(c\) of the original module \(C\). It first unwraps
`WithConv`, takes the ordinary finite dual basis, and transports this basis
back to \(C\) through the evaluation isomorphism
\(C\simeq\operatorname{Hom}_R(\operatorname{Hom}_R(C,R),R)\).
Finite freeness gives the reflexivity used here.

`apply_primalBasis` proves the evaluation identity
\[
 f(c_i)=(b.\operatorname{repr} f)_i\qquad(f\in D).
\]
`primalBasis_coord` identifies the \(i\)-th coordinate functional of \(c\)
with the underlying ordinary linear map of \(b_i\). These two identities are
module statements and do not require a coalgebra structure.

`tensor_coord_comul` then identifies each tensor coordinate of the actual
comultiplication:
\[
 (c\otimes c).\operatorname{repr}(\Delta x)_{(i,j)}=(b_i*b_j)(x).
\]
The proof checks equality of the two linear functionals on pure tensors,
using the coordinate identity and the definition of convolution multiplication.

## Orthogonal idempotents give group-like elements

`repr_one` proves that if the basis \(b\) consists of orthogonal idempotents,
then every coordinate of the convolution unit is one. Indeed, expanding any
\(f\) in the finite basis and multiplying by \(b_i\) gives
\(b_i*f=(b.\operatorname{repr} f)_i b_i\). Substituting the unit and applying
the \(i\)-th coordinate yields the assertion. This auxiliary fact does not
need finite freeness of \(C\); its assumptions are a coalgebra and the given
finite orthogonal idempotent basis of its dual.

The main theorem `isGroupLike_primalBasis` assumes finite freeness of \(C\)
and orthogonality and idempotence of the given finite basis \(b\). For every
index \(i\), it proves both actual equations
\[
 \epsilon(c_i)=1,\qquad \Delta(c_i)=c_i\otimes c_i.
\]
The counit equation follows by evaluating the convolution unit and using
`repr_one`. For the comultiplication equation, equality is checked in the
primal tensor basis. Convolution gives
\(b_i*b_j=0\) for distinct indices and \(b_i*b_i=b_i\); evaluation on a
primal basis vector gives exactly the coordinates of its tensor square.
Completeness of the orthogonal family need not be assumed separately: it is
already a module basis. No local ring or nonzero-idempotent hypothesis is added.

## Provenance and scope

Worker 626 derived this internal algebraic construction from finite dual bases,
evaluation reflexivity, tensor coordinates, and the definitions of convolution
and group-like elements. It makes no additional literature assertion. The
unit recovers a group-like basis from an already supplied finite orthogonal
idempotent basis of the convolution dual. Selecting such a basis from a
spanning family, lifting it through a scalar quotient, and constructing a
multiplicative-type splitting cover are subsequent obligations. This unit does
not prove the fibrewise central-isogeny criterion.
