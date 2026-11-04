# Common-Levi refinements of actual rational geometric intersections

This internal adapter specializes the exact all-test commuting refinement construction to the original standard rational-point subgroups and their forward conjugates. It is a prerequisite for the distinct-radical Haar balance. All declarations are in `Langlands.Aubert.General.RationalPointFamily`.

For any field `k` and group scheme `G`, `IsPointCommutingRefinement P M U Q N V ψ` records five exact rational-point properties:

- `P(ψ)(k) ≤ P`;
- `Z(ψ)(k) = M ∩ N`;
- `U ≤ U(ψ)(k)`;
- `U(ψ)(k) = (M ∩ V) · U`;
- `P(ψ)(k) = (M ∩ Q) · U`.

Here the three dynamic groups are those of the actual cocharacter `ψ`. The two products are products of subsets in the original group `G(k)`, in the displayed order. The predicate does not add semidirect, continuity or Haar properties. The private theorem `pointRefinement_of_dynamic` obtains it by evaluating `Dynamic.IsCommutingRefinement` at the identity test scheme and substituting the six given rational-point identifications.

For the original standard families, write `P_I`, `M_I`, `U_I` and `P_J`, `M_J`, `U_J`. Let `n` be an actual point in the normalizer of the actual torus-point subgroup, and abbreviate the forward conjugates by `Q = n P_J n⁻¹`, `N = n M_J n⁻¹` and `V = n U_J n⁻¹`. The definition `GeometricCommonLeviRefinements i ν I J n ψ θ` records `IsPointCommutingRefinement P_I M_I U_I Q N V ψ`, the reversed predicate `IsPointCommutingRefinement Q N V P_I M_I U_I θ`, and both equalities

`Z(ψ)(k) = Z(θ)(k) = geometricTargetIntersection M_I M_J n`.

The last subgroup is literally `M_I ∩ n M_J n⁻¹`, with its original ambient rational points. Thus the first refined radical is `(M_I ∩ n U_J n⁻¹) · U_I`, and the second is `(n M_J n⁻¹ ∩ U_I) · n U_J n⁻¹`. The respective parabolics are `(M_I ∩ n P_J n⁻¹) · U_I` and `(n M_J n⁻¹ ∩ P_I) · n U_J n⁻¹`. No abstract isomorphism replaces these set equalities.

The theorem `exists_geometric_common_levi_refinements` proves existence of both cocharacters and all these data. Its assumptions are `StandardCocharacterStatement`, connected reductivity of `G`, maximal splitness of `i`, genericity of `ν`, and `HasPointNormalizerComparison i`, at their original scopes. The field and its universe are arbitrary. All `I`, `J` and actual normalizer points are allowed; there is no minimum-representative condition, split or quasisplit restriction, characteristic-zero assumption or local-field topology.

The proof chooses standard cocharacters `α` and `β` using the given standard-cocharacter statement, including all three subgroup-functor identifications. The actual normalizer comparison lifts `n` to a scheme normalizer, whose automorphism of the torus transports `β` to `βn`. The published `groupHom_cocharacterAut_comp` identifies `βn ≫ i` with forward inner conjugation of `β ≫ i`. `Dynamic.rationalPoints_parabolic_conjugate` and the two proved private analogues for centralizers and radicals then give exactly the three forward-conjugate point groups. Both cocharacters factor through the same commutative torus; `Dynamic.range_comp_le_centralizer_comp` supplies their commuting-range condition. Connected reductivity supplies separatedness and smoothness, the latter giving local finite type.

The proof now applies `Dynamic.exists_common_levi_refinements` from `CommutingRefinements`, evaluates the two refinement predicates on rational points, and uses the equality of their ambient centralizer subgroup functors. This gives the two literal common-Levi equalities without any refinement or common-Levi premise.

This construction has internal provenance, consisting of the specialization of the published declarations just named. It imports `RationalGeometricStabilizerProjection` to reuse its actual standard-family and normalizer interfaces; it invokes none of that module's projection-preservation theorems. Its proof bodies use no representation-theoretic geometric lemma, adjointness, cuspidal support, character independence, Langlands classification or Aubert Proposition 3.2. The broader import closure supplies representation interfaces without providing a proof of their geometric-expansion targets.

The distinct-radical modulus balance, continuous coordinates on the refinements and their intersection, normalized coefficient comparison, smooth naturality, compact/full induction comparison, filtration comparison and exact K0 expansion remain separate obligations. This unit proves their algebraic common-Levi refinement prerequisite only.
