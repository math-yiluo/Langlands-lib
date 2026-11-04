# Actual refined radical intersections on rational points

This is an internal derived prerequisite for the rational geometric expansion. It specializes `RefinedIntersection.coordinates` to the original standard rational-point groups. It uses the standard-cocharacter statement, connected reductivity, maximal splitness, genericity and actual point-normalizer comparison; all standard indices `I`, `J` and every actual normalizer point `n` are retained over an arbitrary field in `Type u`.

Write `P = P_I(k)`, `M = M_I(k)`, `U = U_I(k)` and let `Q`, `N`, `V` be the forward conjugates by `n` of `P_J(k)`, `M_J(k)`, `U_J(k)`. Thus these are the literal original subgroups of `G(k)`. The helper `IsSemidirectDecomposition.forwardConjugate` transports the actual decomposition by this forward conjugation. Its continuous-projection helper follows from `continuous_projection_conj`; the private membership comparison identifies subgroup images with the existing conjugate-subgroup convention.

`geometricUnipotentParabolic_eq_mul` proves the exact ordered subset identity

`U ∩ Q = (U ∩ N) (U ∩ V)`.

The proof chooses standard cocharacters for `I` and `J` using the stated standard-cocharacter premise. It transports the second through the scheme normalizer corresponding to `n`; the existing transport theorem identifies its group homomorphism with forward inner conjugation by the same ambient point. The three dynamic point subgroups are then exactly the original `U`, `Q`, `N`, `V`. Evaluating the proved common-torus intersection products at the identity test scheme gives the displayed identity. Separatedness is obtained from connected reductivity. No extra subgroup-product premise is added.

Suppose `ψ`, `θ` have `GeometricCommonLeviRefinements i ν I J n ψ θ`, the refinement data constructed by `exists_geometric_common_levi_refinements` in the imported adapter. Put `R = U_ψ(k)` and `S = U_θ(k)`. `geometricRefinedRadicalIntersection_eq_mul` proves

`R ∩ S = (M ∩ V) ((U ∩ N) (U ∩ V))`.

It specializes the generic three-factor intersection lemma. Its two refined-radical product hypotheses are clauses of the actual refinement data. The containment `S ≤ Q` follows from `U_θ ≤ P_θ` and the refinement parabolic containment. The remaining radical–parabolic product is the theorem just proved. Every equality is equality of subsets of `G(k)` with the displayed noncommutative order.

For any topological-group topology on `G(k)`, original semidirect decompositions `dI`, `dJ`, and continuous original Levi projections, `geometricRefinedRadicalIntersectionCoordinates` constructs a homeomorphism

`(M ∩ V) × ((U ∩ N) × (U ∩ V)) ≃ₜ R ∩ S`.

It applies the generic coordinate construction to `dI` and the forward conjugate of `dJ`; continuity of the latter projection is derived from that of `dJ`. All subgroup topologies are inherited from the same ambient topology. The apply theorem identifies the forward value in `G(k)` as `b * (a * c)`. This is a homeomorphism of spaces with multiplication as its forward map. Its inverse is the generic construction from the restricted original projections.

No local compactness, closedness, Haar measure or determinant formula is asserted here. In particular the common-Levi squared-modulus identity, normalized coefficient comparison and final exact K0 expansion remain separate proof obligations. The refinement premise in the coordinate theorem is the explicit constructed algebraic data; it is not an assumed modulus or geometric-expansion conclusion.
