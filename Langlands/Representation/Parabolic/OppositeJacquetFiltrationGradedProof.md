# Proof of the normalized opposite image-filtration graded comparisons

The theorem `Langlands.Parabolic.normalizedOppositeJacquetFiltrationGraded`
proves the exact proposition
`Langlands.Parabolic.NormalizedOppositeJacquetFiltrationGradedStatement`
from `Langlands.Representation.Parabolic.OppositeJacquetFiltrationGradedStatement`.
The field universe `uF` and representation-carrier universe `uV` are independent.

The proof uses ordinary coinvariant exactness. In the namespace
`Langlands.Jacquet.OppositeImageGradedProof`, `normalizedImageGraded` establishes
the general algebraic comparison for a subgroup whose finite subsets lie in
compact open subgroups. The input representation is smooth. The private
`normalizedMap_injective` applies
`Langlands.coinvariants_map_injective_of_smooth` to the inclusion of an invariant
subspace in the ambient representation. Thus `stepImageEquiv` identifies the
coinvariants of each original step with its actual image in the ambient
coinvariants.

For adjacent steps, `adjacent_exact` identifies the range of their inclusion
with the kernel of the original graded projection. The private
`adjacent_image_kernel` applies `Langlands.coinvariants_map_range_eq_ker` to this
sequence and uses injectivity into the ambient coinvariants. It identifies
the inverse image of the actual lower image with the kernel of the map to
the original graded-piece coinvariants. Composing that map with the inverse
of `stepImageEquiv` gives a surjection from the actual upper image with exactly
the actual lower image as kernel.

`MultiplicityAdditivityProof.quotient_equiv_of_surjective` then descends this
surjection to an equivalence from the actual graded quotient. All actions
pull back the normalizer action and twist by the same unit-valued character.
The intertwiners retain their original linear maps, so the argument preserves
the actual normalized actions without changing carriers or filtration indices.

The refined specialization uses
`T.refinedOppositeUnipotent_finite_containment`. For the composed specialization,
`Parabolic.flattenedOppositeUnipotentComparison` identifies the actual radical
with the opposite radical of the flattened shape. The published theorem
`CuspidalJacquetMultiplicity.oppositeUnipotent_finite_containment` then supplies
finite containment. The proof uses no compact-subset containment, extra
admissibility or supplied exactness assumption.

Each original index is retained: the proof identifies the quotient of the two
fixed adjacent image steps, including repeated steps and zero quotients, with
the normalized Jacquet representation of the original graded quotient. The
normalizer maps and inverse half characters are exactly those of the published
refined and composed opposite functors. In particular, the composed action
retains both outer and inner modulus factors. No positive-rank or nonzero-length
restriction is added.

This is an internal algebraic prerequisite for constituent comparisons. It
does not prove a multiplicity comparison or the host's irreducible-head
consequence, and makes no claim to reproduce a separate literature theorem.
