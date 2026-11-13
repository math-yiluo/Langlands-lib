# Finite-source Hermitian presentations identify the actual model

This internal construction completes the coordinate-to-scheme comparison used
by Task 5813. It takes a separable quadratic extension `L/k`, two finite index
types `Source` and `Middle`, and a diagonal Hermitian form `H` on `Middle`.
The fields have arbitrary common universe `u`, while the finite index types
lie in `Type`. There is no characteristic assumption and no anisotropy
assumption on `H`.

The input coordinate matrices are
`P : Matrix (Index Middle) Source L` and
`Q : Matrix Source (Index Middle) L`, with both `PQ = 1` and `QP = 1`.
A source matrix `J` is related to the actual full model Gram matrix by
`(P.map bar).transpose * gram H * P = J`. No matrix entry is replaced by a
self-pairing condition. The middle block of `gram H` has the existing negative
weight convention.

For an actual group scheme `G`, the other input is a monoid homomorphism
from `(T ⟶ G.X)` into the general-linear group over the actual tensor
coefficient ring, for every test scheme `T`. Each map is injective. Its range
is exactly all invertible matrices `g` satisfying the full equation
`g* J_T g = J_T` and `det g = 1`, where `J_T` is the entrywise extension of
`J` and `g*` is conjugate transpose for the tensor involution. Finally,
these maps must commute entrywise with every actual test restriction. These
are supplied presentation hypotheses, not conclusions from an index.

## Implemented construction

`tensorRectangularMatrix` extends any rectangular field matrix entrywise into
the actual tensor coefficient ring. `tensorRectangularMatrix_map` proves
naturality because test restriction fixes `a ⊗ 1`.
`tensorRectangularMatrix_mul` extends either coordinate inverse identity.
`tensorRectangularGramCongruence` extends the supplied Gram congruence: ring
maps preserve products, `gram_map` extends the actual weights, and the
published `tensorInclusion_bar` checks compatibility with conjugation.

`tensorRectangularConjugation` applies the imported rectangular multiplicative
equivalence to each test ring. Its value is `P_T g Q_T`. The imported full
Gram-equation equivalence and determinant preservation prove
`tensorRectangularConjugation_mem_iff`: the raw two equations are equivalent
to membership in `specialUnitarySubgroup (tensorForm k L H T)`.

`finitePresentationHom` composes the raw presentation with this coordinate
conjugation and restricts to the actual subgroup. The forward range implication
proves that it lands there. Raw injectivity and injectivity of coordinate
conjugation prove faithfulness. For surjectivity, transport a target unitary
matrix back through the coordinate equivalence, use the membership equivalence
to verify the raw equations, and use the reverse range implication to obtain
an actual point of `G`. `finitePresentationEquiv` packages this bijective
homomorphism as a multiplicative equivalence.

`finitePresentationEquiv_val` records the explicit value `P_T ρ_T(x) Q_T`.
Together with the raw naturality and constant-coordinate naturality, this
proves `finitePresentationEquiv_naturality` on every test scheme. With supplied
unit witnesses for the weights of `H`, `isoOfFinitePresentation` applies the
published `isoOfMatrixPoints` to obtain

`G ≅ HermitianRoot.SchemeModel.groupScheme k L H w hw`.

The result is an actual group-scheme isomorphism because `isoOfMatrixPoints`
uses these natural equivalences on every test scheme. No affineness or finite
type assumption on `G` is needed for this conditional construction.

## Provenance and remaining obligations

This is internal infrastructure derived from explicit matrix algebra and the
published Hermitian point-model comparison. It transcribes no classification
result from external literature. The quadratic extension, full presentation
and Gram coordinates remain inputs. This unit does not construct a presentation
from a Tits index, compare split rank with isotropic dimension, or prove the
host `OuterTypeARankOneHermitianStatement`.
