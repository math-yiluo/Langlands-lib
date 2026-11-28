# The Galois last break of an ℓ-adic representation

For any prime \(\ell\) and finite-dimensional algebraic action over `PadicAlgCl ℓ`,
`ladicGaloisLastBreak` takes the real `sInf` of the nonnegative indices
at which the actual upper ramification group acts trivially. A
nonempty threshold set is bounded below by zero and its infimum is
the usual last upper break. An empty threshold set gives zero by
`Real.sInf_empty`.

At nonnegative indices the upper group lies in absolute inertia. Its
elements lift through the inclusion of inertia in the local Weil
group. Extension of scalars to \(\mathbb C\) is injective on
endomorphisms. The restricted, extended action therefore has the
same threshold set. When the extended Weil action is continuous,
`weilTrivialityThresholdsNonempty` gives a threshold for both actions.

`hasWeilSwan_iff_ladicGaloisLastBreak` takes a continuous irreducible
Weil class \(\sigma\) of rank \(k+1\) whose underlying isomorphism
class equals the class of \(A\) restricted from Galois to Weil and
extended through the supplied coefficient embedding. It identifies
`HasWeilSwan` at the natural exponent \(s\) with the equality in
\(\mathbb R\) of \(s\) and \((k+1)\) times the Galois last break of
\(A\). The formula includes \(s=0\).

`ladicHasSwan_iff_ladicGaloisLastBreak` and
`ladicHasSwan_iff_of_embeddings` use `LadicWeilTransportStatement`
and assume that \(\ell\) differs from the residue characteristic.
The first applies the formula to the class witnessing `LadicHasSwan`
in the forward direction and obtains the Weil class from the
transport theorem in the reverse direction. The second compares the
two embeddings using the same Galois representative.

The definition extends the slope formula for continuous finite-model
representations in `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§4.1, printed pp. 509–510 (PDF pp. 14–15). Section 4.2 compares
conductors of finite-image Galois classes across coefficient fields.
The Swan comparison here is derived from equality of the last upper
breaks after restriction and scalar extension for a certified
continuous irreducible Weil transport.
