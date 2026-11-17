# Normalizer cosets and source automorphisms of two conjugation families

Let `i : H.toGrp → G` be a homomorphism from a commutative group scheme,
with monomorphic underlying scheme map. Over every base scheme and every
relative test `T`, two points `g,h` have conjugation families differing by
an actual automorphism of `H_T` if and only if `g⁻¹ * h` belongs to the
full all-refinement normalizer of `i`.

`exists_sourceIso_conjugationFamily_eq_iff` states this exact equivalence.
`normalizerPairSourceIso` chooses the source automorphism from a supplied
normalizer-coset membership and retains the equality of actual relative
group-scheme morphisms. No smoothness, finiteness, or multiplicative-type
hypotheses are required.

The proof composes the first conjugation family with the inverse inner
automorphism associated to `h`. The anti-multiplicativity of inner
automorphisms identifies this with conjugation by `h⁻¹ * g`. A purely
categorical cancellation lemma removes the common target isomorphism.
The single-family criterion from `NormalizerConjugation` then identifies
the result with normalizer membership. Inversion in the normalizer
subgroup exchanges `h⁻¹ * g` with `g⁻¹ * h`.

The implementation factors the inner-automorphism identity through
explicit equalities for an abstract group homomorphism of points. This
keeps the actual pullback point comparison as a single supplied map.
All provenance is internal and derived from the imported conjugation,
normalizer, and inner-automorphism constructions.
