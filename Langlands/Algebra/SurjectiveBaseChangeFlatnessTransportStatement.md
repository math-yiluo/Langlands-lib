# Transport of fibre-module flatness across a surjective algebra map

`Langlands.Algebra.SurjectiveBaseChangeFlatnessTransportStatement` is a
proposition definition, not a proof.

Let R, A, S and T be commutative rings, with compatible algebra structures
R to A to S and R to T. Let M be an S-module with a compatible A-module
structure. Assume that the actual structure map A to S is surjective and that
the actual base-change map

`A tensor_R T -> S tensor_R T`

is bijective. This map sends `a tensor t` to `image(a) tensor t`; in Lean it is
`Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A S) (AlgHom.id R T)`.
Then flatness of `(S tensor_R T) tensor_S M` over `S tensor_R T` implies
flatness of `(A tensor_R T) tensor_A M` over `A tensor_R T`.

The statement retains the actual base-change modules and their canonical
left-factor actions. Its five universe parameters are independent. It imposes
no locality, finiteness, Noetherianity, nontriviality, or flatness over R.
Surjectivity of A to S is an explicit hypothesis; an unrelated isomorphism
between the two fibre rings is not sufficient input to this statement.

## Derived provenance and role in 05UV

This is an elementary supporting implication in the proof of Stacks Project,
Lemma 10.128.9, tag 05UV. There A is B/J', S is B/J, T is the residue field
R/m, and the map A to S is the canonical surjective quotient comparison.
After choosing J' so that the fibre-ring comparison is an isomorphism, the
source applies Lemma 10.128.8 to R to B/J' to S' and M. The fibre-module
flatness assumption needed in that application is exactly the transport
expressed here.

The statement generalizes this step to arbitrary T. To see why the
generalization is valid, put C = A tensor_R T and D = S tensor_R T.
Use the specified bijection C to D to regard D as a flat C-algebra.
Restriction of scalars therefore makes the given flat D-module
D tensor_S M flat over C. Surjectivity of A to S identifies
D tensor_A M with D tensor_S M, preserving the C-action. The bijective
map C to D also identifies C tensor_A M with D tensor_A M as C-modules.
Combining these identifications yields the asserted flatness.

This provenance argument explains the generalization; the Lean file does not
prove it. This statement neither establishes the bijectivity hypothesis nor
the local flatness criterion, and it does not complete 05UV.

Source: registered `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
`05UV.html`, proof of Lemma 10.128.9, the displayed quotient-fibre isomorphism
and the immediately following application of Lemma 10.128.8.
