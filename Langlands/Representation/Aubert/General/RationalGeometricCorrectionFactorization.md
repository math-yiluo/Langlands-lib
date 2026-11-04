# Actual geometric correction intersections and their Haar products

This is an internal derived construction for the rational geometric-lemma proof. It uses the published original Levi-projection preservation theorem in `RationalGeometricStabilizerProjection` and the continuous semidirect Haar product theorem in `SemidirectRestriction`. It does not assert the final normalized K0 expansion.

For an original semidirect decomposition `P = M ⋉ U` and a subgroup `F` preserved by the original projection, `IsSemidirectDecomposition.interOfProjection` constructs the decomposition

`P ∩ F = (M ∩ F) ⋉ (U ∩ F)`.

The proof restricts the normalizer law and uses uniqueness of the original decomposition. `interOfProjection_projection` proves that the new projection has exactly the original ambient group value. Its continuity therefore follows by restriction of the original continuous projection. No decomposition or projection of the intersection is assumed.

For the actual rational standard family, `geometricCorrectionIntersectionDecomposition` specializes this construction to

`P_I ∩ n U_J n⁻¹ = (M_I ∩ n U_J n⁻¹) ⋉ (U_I ∩ n U_J n⁻¹)`.

Here `n` is an actual point normalizing the original torus; all intersections retain their original ambient rational points. The premises are connected reductivity, the original maximal split torus and generic cocharacter, `StandardCocharacterStatement`, point-normalizer comparison and the supplied original `P_I = M_I ⋉ U_I` decomposition. Every `I`, `J`, and actual normalizer point is allowed; no minimal representative is needed. The field has no characteristic or split-group restriction. With a supplied ambient topological group structure and continuity of the original projection, `geometricCorrectionIntersectionCoordinates` is the homeomorphism from the product of the two literal intersection factors to the correction intersection, given by multiplication. The ambient topology is arbitrary in these constructions.

`geometricCommonLevi_normalizes_intersection` derives normalization of `U ∩ n V n⁻¹` by `M_I ∩ n M_J n⁻¹` from normalization of `U` by `M_I` and of `V` by `M_J`. It uses the original conjugation homomorphism and the normalizer law for an intersection.

For a locally compact, second countable ambient topological group, `interOfProjection_closedRestrictCharacter` gives the product of the actual closed-subgroup Haar characters under these continuous coordinates. Its closedness assumptions concern the original `P`, `M`, `U`, and `F`; the intersection closedness is derived. The proof applies the published continuous semidirect Haar product theorem to the constructed intersection decomposition.

The rational specialization `geometricCorrectionIntersection_modulus_eq_mul` is an equality of positive, units-valued Haar characters on the actual ambient common Levi `L = M_I ∩ n M_J n⁻¹`:

`δ_(P_I ∩ n U_J n⁻¹)|L = δ_(M_I ∩ n U_J n⁻¹)|L · δ_(U_I ∩ n U_J n⁻¹)|L`.

It requires closedness of the original `P_I`, `M_I`, `U_I`, and `U_J`, continuity of the original `I` projection, and the original `J` semidirect decomposition. All three normalizer witnesses are derived from the original decompositions; no additional normalizer or modulus identity is a premise. The equality uses the existing `HaarModulus.closedRestrictCharacter`, with its original conjugation direction and canonical positive Haar convention. The character domain is the ambient subgroup `L`; restricting along its canonical point-preserving identification with `L.subgroupOf M_I` gives the same values on the literal nested common Levi used by the geometric functor. Swapping `I`, `J` and using `n⁻¹` gives the inverse-oriented version. The explicit second-countability hypothesis in the Haar theorem is available for the host's exact reductive rational-point topology from the imported `reductiveRationalPoint_secondCountable`; the topological coordinates do not need it.

This unit supplies one actual correction-intersection factorization and its symmetric specialization. It does not establish the distinct-radical squared-modulus balance, identify the fully normalized coefficient, compare compact with full induction, construct an ordered orbit filtration, or prove the exact K0 sum. Those remain obligations of the host task.
