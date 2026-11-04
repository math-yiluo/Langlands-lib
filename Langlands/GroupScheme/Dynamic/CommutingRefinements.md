# Common-Levi refinements of commuting dynamic parabolics

This internal construction derives exact subgroup-functor identities from the published commuting cocharacter combination, dominant-inclusion theorem and nested decomposition. It is a prerequisite for the distinct-radical normalization balance in the rational geometric lemma. All declarations are in `Langlands.GroupScheme.Dynamic`.

Write `P(χ)`, `Z(χ)` and `U(χ)` for the published dynamic parabolic, centralizer and identity-limit subgroup functors. The definition `IsCommutingRefinement χ τ ψ` records the following actual ambient data:

- `P(ψ) ≤ P(χ)`, `Z(ψ) = Z(χ) ∩ Z(τ)` and `U(χ) ≤ U(ψ)`;
- on every test scheme `X`, the set equality `U(ψ)(X) = (Z(χ) ∩ U(τ))(X) · U(χ)(X)`;
- on every test scheme `X`, the set equality `P(ψ)(X) = (Z(χ) ∩ P(τ))(X) · U(χ)(X)`.

The products are products of subsets of the original group of `X`-points, in the displayed order. This definition does not assert normal-complement or topological properties.

For any base scheme, `range_le_centralizer_symm` proves symmetry of the commuting-range condition `range τ ≤ Z(χ)`. The proof uses `torusCentralizer_gm_eq_dynamicCentralizer` to express centralizer membership as commutation after every change of test scheme. Applying the given condition to every value of `τ` and reversing commutation proves the opposite inclusion `range χ ≤ Z(τ)`.

On `Z(χ)`, the combination `χⁿτ` acts exactly as `τ`, by `orbit_cocharacterCombination_of_mem_centralizer`. The three restriction lemmas `centralizer_inf_parabolic_combination`, `centralizer_inf_unipotent_combination` and `centralizer_inf_centralizer_combination` therefore identify its intersections with `Z(χ)` with those of `τ`. These restriction identities require no field, finite-type or separatedness hypothesis.

The dominant centralizer inclusion identifies the combination's centralizer with the literal intersection in `centralizer_combination_eq_inf`. With a separated ambient group and the two inclusions `P(χⁿτ) ≤ P(χ)` and `U(χ) ≤ U(χⁿτ)`, `unipotent_combination_eq_inter_mul` and `parabolic_combination_eq_inter_mul` apply the published nested product lemmas from `NestedDecomposition` and the restriction identities above. This proves both exact same-test products.

For an affine, separated group scheme locally of finite type over any field, `exists_commuting_refinement` uses `exists_dominant_inclusions` from `DominantCombinationInclusions` to choose a sufficiently dominant integer combination and prove all fields of `IsCommutingRefinement`. The cocharacters need only satisfy the commuting-range condition; reductivity, splitness and characteristic zero are not assumed. The universe of the field is arbitrary.

Finally, `exists_common_levi_refinements` applies this existence theorem in both orders, using the proved symmetry. It returns cocharacters `ψ` and `θ`, both exact refinement predicates, and equality `Z(ψ) = Z(θ)`. The first predicate identifies this common subgroup functor with `Z(χ) ∩ Z(τ)`; the second identifies it with `Z(τ) ∩ Z(χ)`. The equality is proved by commutativity of intersection on every test scheme, without a chosen isomorphism or a common-Levi premise.

This unit has internal provenance: the implemented proof is a direct consequence of the published cocharacter and nested-decomposition declarations just named. Its proof bodies use no representation-theoretic geometric lemma, adjointness, cuspidal support, character independence, Langlands classification or Aubert Proposition 3.2. It establishes no Haar modulus identity, rational standard-subgroup identification, representation comparison or K0 expansion; these remain separate obligations.
