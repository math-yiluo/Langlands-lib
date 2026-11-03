# Proof of the trace-class ideal laws

`Langlands.Analysis.OperatorIdeals.traceClassIdeal` proves
`TraceClassIdealStatement` for independent arbitrary space universes.
The file also exposes individual zero, addition, scalar, adjoint,
rectangular-sandwich and ordinary pre/postcomposition theorems.

For zero, apply trace-class membership of Hilbert–Schmidt products to
two zero maps. For each nonzero-law argument, first use
`traceClassFactorization` to write a given trace-class endomorphism
A as U V with both factors Hilbert–Schmidt. Scalar multiplication acts
on U. Taking adjoints reverses the two factors. For a bounded sandwich
B A C, use the Hilbert–Schmidt factors B U and V C. The corresponding
Hilbert–Schmidt laws preserve membership in every case, and
`hilbertSchmidtProductTraceClass` proves trace-class membership of the
new product. Double adjoint proves the converse adjoint implication.
The ordinary endomorphism ideal laws follow by setting one sandwich
map to the identity.

For addition, factor A=U₁ V₁ and D=U₂ V₂. On
H=`WithLp 2 (E × E)`, let I and J be the two bounded inclusions and
let p and q be the bounded coordinate projections. Then
R=I V₁ + J V₂ maps E to H, and Q=U₁ p + U₂ q maps H to E.
Both maps are Hilbert–Schmidt by bounded composition and addition.
The actual square-sum norm makes H a complete complex inner-product
space. Coordinate simplification gives Q R=A+D, so rectangular
Hilbert–Schmidt product membership finishes the proof.

The proof uses no spectral decomposition, trace linearity or trace-norm
triangle inequality. The statement Markdown records its internal
provenance and the precise source and scope boundaries.
