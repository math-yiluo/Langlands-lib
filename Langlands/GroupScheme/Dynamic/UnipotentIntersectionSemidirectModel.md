# Semidirect realization of an actual unipotent intersection

This is an internal construction by Worker 184. All subgroup identities are
identities of functors on every test scheme over an arbitrary base scheme.
No smoothness, reductivity, field or rational-point topology is assumed.

For an automorphic action `a` of `H` on `N`, suppose the cocharacter `chi`
of `H` is central: `Dynamic.centralizer chi = top`. Then projection from the
actual semidirect product to `H` is invariant under conjugation by the lifted
cocharacter `chi` followed by `a.semidirectInr`. The proof computes the
projection of conjugation and uses centrality of each cocharacter value.
The acting group itself need not be commutative.

If `H` is separated, this invariance forces every point with identity limit
to lie in the normal factor. The existing equivariant closed-inclusion
comparison consequently identifies the image of the identity-limit functor
of `a.restrict chi` with the entire dynamic unipotent functor in the semidirect
group. `isRepresentedBy_semidirectInl_comp_of_central` expresses the same
identity using any displayed representative, retaining its original group
scheme. Both the whole acting factor and any homomorphism through that factor
centralize the lifted central cocharacter; the two range lemmas record these
containments on every test scheme.

The intersection application has cocharacters `chi` and `psi` of `G`.
The closed inclusion `iH : H -> G` has range contained in both centralizers.
There is a displayed lift `chiH` with `chiH` followed by `iH` equal to `chi`.
The closed inclusion `iN : N -> G` represents `U(psi)`. The inclusion
`iU : U -> G` represents the literal functor intersection
`U(chi) intersect U(psi)`, and `fU : U -> N` followed by `iN` equals `iU`.
These representatives and factorizations are hypotheses; their existence is
not asserted here.

The lift `chiH` is central in `H`, by the closed-subgroup centralizer
preimage identity. Let `a` be the actual conjugation action of `H` on `N`.
Its restriction along `chiH` intertwines `iN` with conjugation by `chi`.
The closed-subgroup identity-limit comparison and reflection of the displayed
range through the monomorphism `iN` show that `fU` represents the identity-limit
functor of this restricted action. If `H` is separated, composing `fU` with
`a.semidirectInl` therefore makes this same `U` a representative of the
dynamic unipotent subgroup for `chiH` followed by `a.semidirectInr`.

`semidirectUnipotentIntersectionAction` is the actual conjugation action on
this representative by any map `fZ : Z -> H`, computed inside the semidirect
group. If `fZ` followed by `iH` is `iZ : Z -> G`, whose range centralizes both
original cocharacters, `semidirectUnipotentIntersectionAction_eq` identifies
this action with `centralizingUnipotentIntersectionAction` in `G`.
The proof first composes with the normal-factor inclusion and uses the
semidirect conjugation formula. Cancellation of that monomorphism identifies
the induced action on `N`. Composition with `iN` then gives the original
forward conjugation formula `z*x*z^-1` in `G`; cancellation of `iU` proves
equality of the actual actions on the same `U`.

This is a model and action comparison for the positive/positive intersection.
It does not establish the existence of the displayed models, smooth affine
topologies, a Haar determinant identity, character detection on a whole Levi,
or the normalized exact-K0 geometric expansion.
