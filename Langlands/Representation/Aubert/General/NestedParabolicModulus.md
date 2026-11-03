# Haar-modulus multiplication for nested actual parabolics

This internal prerequisite proves the analytic product and actual-subgroup transport used by normalized nested transitivity. It is a generic topological-group argument, independent of representation-carrier universes and of reductive geometry. Its inputs include the actual supplied radical product; it does not prove that structural product or either natural functor isomorphism.

Write `Q = L ⋉ U` and let `N ≤ Q`. Assume the literal set identity `N = (L ∩ N) U`. The lemma `unipotent_le` reads off `U ≤ N`. To prove `projection_mem`, decompose an element of `N` into a factor in `L ∩ N` followed by a factor in `U`; the characterization of the existing outer Levi projection identifies that first factor with the projection.

`radicalDecomposition` proves the semidirect decomposition `N = (L ∩ N) ⋉ U`. Normalization comes from `N ≤ Q`. Existence and uniqueness of the first factor follow from the outer projection and its uniqueness characterization. `radical_projection` identifies the resulting canonical projection with the outer one, as actual ambient group elements. Accordingly `continuous_radical_projection` proves continuity using exactly the existing subspace topologies and the assumed continuity of the outer projection.

`ambient_modulus_product` assumes a locally compact, second-countable topological ambient group and closedness of `N`, `U` and `L`. For any subgroup `S ≤ L` normalizing `N`, it proves pointwise that the positive Haar modulus on `N` equals the product of the moduli on `L ∩ N` and `U`. The lemma `normalizes_inter` supplies preservation of the intersection. The proof applies the published semidirect-coordinate Haar-product theorem to the preceding radical decomposition. Conjugation by the same element of `S` respects those coordinates by the group laws. The Haar characters and their orientation are exactly the existing `HaarModulus.closedRestrictCharacter` definitions.

`interSubgroupOfEquiv` is the continuous multiplicative equivalence between the ambient intersection `L ∩ N` and the literal copy `N.subgroupOf L`. It sends the same ambient element to the nested subtype. `normalizes_subgroupOf` supplies the corresponding normalizer condition inside `L`. Finally, `inner_modulus_eq` proves that the inner restricted Haar character, pulled back to an actual subgroup `S ≤ L`, equals the ambient intersection character. The conjugation automorphisms commute with this explicit equivalence, and the published invariance of `mulEquivHaarChar` under continuous group transport proves the equality. This last transport requires local compactness and closedness, but no second-countability assumption.

These are derived laws of the existing actual-subgroup and Haar APIs. The topological and structural premises remain visible. In the dynamic application they are to be discharged from the target's hypotheses and existing canonical-point results; no modulus factorization is added to that target.

Normalizer containment for the subgroup copy uses the existing
`Langlands.Aubert.General.normalizes_subgroupOf` from `SubgroupOfModulus`.
