# Opposite Jacquet counts along a flattened shape

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiCount`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

- `oppositeFunctor_map_injective`, `oppositeFunctor_map_surjective`: the published
  opposite Jacquet functor `CuspidalJacquetMultiplicity.oppositeFunctor T C` maps
  injective (surjective) morphisms of smooth representations to injective (surjective)
  maps. It preserves monomorphisms and epimorphisms by the instances of
  `CuspidalJacquetFunctorExactnessProof`.
- `count_flattened`: a multiplicity in the composed opposite Jacquet module along
  `(B, S)` is the same multiplicity in the opposite Jacquet module along `B.flatten S`.
  The test representation is pulled back along `flattenedLeviEquiv`. Proof: published
  `flattenedOppositeJacquetComparison` and the two multiplicity transport theorems.
- `quotient_count_ge`: let `μ` be an irreducible admissible representation of the Levi
  of `B`. Suppose a test representation `τ` of the refined Levi has the same
  multiplicity `m` in the inner and ambient opposite Jacquet modules of `μ`. Then every
  irreducible smooth quotient `P` of the normalized induction of `μ` has a multiplicity
  `c ≥ m` of the pulled-back `τ` in its opposite Jacquet module along `B.flatten S`.
  This is the argument inside the published `glRelativePositiveTotalHead`:
  - `P` is admissible;
  - normalized second adjointness turns `Ind μ ↠ P` into an injection of `μ` into the
    opposite Jacquet module of `P`;
  - refined Jacquet functors keep it injective, and transitivity gives an injection of
    the inner Jacquet module of `μ` into the composed Jacquet module of `P`, which
    therefore has count at least `m`;
  - the composed Jacquet module of `P` is a quotient of that of `Ind μ`, which has
    count `m`; by uniqueness of multiplicities its count is the same `c`.
- `count_pos_of_isSubquotient`: an irreducible subquotient `τ` of a finite-length
  representation `A` has positive multiplicity in `A`. Proof: counting lemmas of
  `HeadDetectingCount` along `U ↪ A`, `U ↠ τ` and `irreducibleMultiplicity`.
