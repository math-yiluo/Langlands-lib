# A finite-type-point criterion for global etale slices

For any universe `u`, schemes `U` and `R` in `Scheme.{u}`, and morphisms
`t s : R ⟶ U`, suppose the following holds for every point `x` of `U` whose
canonical residue-field morphism is locally of finite type: there exist a
scheme `V` in the same universe and a locally finite type morphism `g : V ⟶ U`
such that `pullback.snd g t ≫ s` is etale and its image contains `x`.
Then there exist a scheme `V` in the same universe and a locally finite type
morphism `g : V ⟶ U` such that `pullback.snd g t ≫ s` is both etale and
surjective.

This is an internal globalization interface for the etale slicing task,
suggested by Worker 303's finite-type-point reduction. It makes no smoothness
or equivalence-relation assumption and asserts no local slice construction.
The finite type point condition means precisely
`LocallyOfFiniteType (U.fromSpecResidueField x)`, not a condition on the
absolute residue-field extension. All morphism properties and pullbacks are
the existing Mathlib ones.

The expected proof takes the coproduct of one local slice for each point
satisfying this condition. The index is a subtype of the underlying points of
`U`, so the coproduct stays in `Scheme.{u}`. Source locality preserves local
finiteness of type and etaleness. The resulting image is open. An open subset
containing all these points is all of `U`: otherwise, an affine chart of its
nonempty closed complement contains a closed point, whose residue-field map
into `U` is locally of finite type. This is an internal consequence of Mathlib's
scheme, compactness and morphism-property results, not a new imported
literature theorem. No quotient or unproved Library statement is assumed.
