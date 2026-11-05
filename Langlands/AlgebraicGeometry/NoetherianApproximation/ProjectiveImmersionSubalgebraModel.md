# Models retaining a specified projective immersion

Let F be any field, X a scheme whose underlying space is quasi-compact
(`CompactSpace X` in Lean), and j : X → Pⁿ_F a specified immersion. The constructor
`projectiveImmersionSubalgebraModel F X n j` produces an actual model over a
finitely generated integer subalgebra A ⊆ F. The field and schemes lie in one
arbitrary common universe. There is no characteristic or separability
restriction, and n may be zero.

The result has type `ProjectiveImmersionSubalgebraModelData F X n j`. Its fields
give the literal subalgebra A of the original field and its finite generation,
a scheme X_A, an immersion m : X_A → Pⁿ_A in the same projective dimension, and
a comparison p : X → X_A. The structure morphism m followed by Pⁿ_A → Spec A
is locally of finite presentation and quasi-compact. The square with top map p,
left map j followed by Pⁿ_F → Spec F, right map the structure morphism of X_A,
and bottom map Spec F → Spec A for the original inclusion is Cartesian.
Furthermore, p followed by m equals j followed by the canonical coefficient
map Pⁿ_F → Pⁿ_A. Thus the model retains the given immersion, not just an
unspecified generic-fiber isomorphism.

This is a derived prerequisite for the model step of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed pp.9–10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad chooses a quasi-projective model outside finitely many places before
forming its integral Weil restriction. The present construction supplies the
finite coefficient step for a specified projective immersion over any field.
Realizing those coefficients in actual arithmetic S-integers, arranging a common
model for a field extension, and the adelic comparison remain separate.

The private `closure_model` first takes the scheme-theoretic image of j.
Quasi-compactness of X and quasi-separatedness of projective space make j
quasi-compact, so its image inclusion is a closed immersion. Over the field,
the image structure morphism is flat and locally of finite presentation.
The published theorem
`ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`
descends this projective closure over a finitely generated integer subalgebra,
with both its Cartesian comparison and its original projective-map equality.

In `model_nonempty`, X identifies with a quasi-compact open in that closure's
original-field pullback. The published
`exists_fg_subalgebra_opens_preimage_eq_of_isCompact` descends this open after a
finitely generated coefficient enlargement. Pullback cancellation identifies the
coefficient transition square; the preimage equality makes the open square
Cartesian. Pasting gives the required original-field square. The projective
coefficient pullback constructs the enlarged closed immersion, and restricting
it to the descended open gives m. Its structure morphism is locally of finite
presentation by base change and composition, and quasi-compact because its
source is quasi-compact. The two projections of the projective coefficient
pullback establish the original-immersion equality. Restricting scalars along
the two finite coefficient enlargements gives finite generation over ℤ.
Finally, the public constructor chooses from this proved nonempty collection;
model existence is not an additional premise.
