# Algebraic bounds for Chevalley root filtrations

Worker 312. This is derived internal content for the depth-zero unramified
root-filtration boundedness task. It is obtained from the published polynomial
bounded-evaluation lemma, vector-group coordinates and the Chevalley root-family
identities. It is not asserted as a separate quotation from the literature.

`ChevalleyZeroRootFiltrationBoundedStatement`, at arbitrary universe `u`,
quantifies over a reduced root datum with finitely many roots and finite free
character lattice, Chevalley data and its actual Chevalley group over any
valuative field. The group is assumed affine and locally of finite type. Given
an additive valuation into `WithTop ℝ` inducing the prescribed valuative
relation in the opposite order, every zero-depth filtration of its Chevalley
root function family, for every relative root of its actual split torus, is
algebraically bounded in the group. The theorem
`chevalleyZeroRootFiltrationBounded` proves this proposition.

The vector-group helper bounds every regular function from uniform bounds on
the standard affine coordinates. Its proof uses the polynomial presentation of
the vector group and the published bounded-evaluation subalgebra.

The root-coordinate helper applies that result to the actual additive-group
points attached to field elements and maps them through the actual Chevalley
root homomorphism. The root-filtration helper then rewrites the Chevalley family
as the additive valuation of its root coordinate. A field element whose
valuation is at most the specified real depth gives a uniform valuative bound
on all allowed coordinates. The valuative relation is explicitly required to
agree with the additive valuation in the opposite order. At depth zero, the
unit scalar always supplies the required bound because its additive valuation
is zero; the corresponding corollary therefore needs no scalar-existence
hypothesis.

These helpers do not yet construct bounded quasi-split apartments or prove the
unconditional unramified target. They use no compactness, completeness or
restriction on the residue field.
