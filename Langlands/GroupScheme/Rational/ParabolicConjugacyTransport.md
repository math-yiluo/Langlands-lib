# Rational conjugacy and transport of standard-parabolic indices

This is derived infrastructure for
`StandardParabolicClassificationStatement`. It does not prove that statement
or assume a structural classification theorem. Its inputs are the published
subgroup functors, their `comap`, the actual rational-point inner automorphisms
and the published dynamic functoriality theorem. No additional literature
assertion is introduced.

For a group scheme `G` over an arbitrary base scheme `S`,
`SubgroupFunctor.IsRationallyConjugate P Q` means that there is a point
`g : S ⟶ G` such that `P = Q.comap (G.innerIso g).hom`. More precisely the
point is a morphism from `Over.mk (𝟙 S)` to `G.X`. This is equality of subgroup
functors on **every test scheme**, rather than equality only at the base.
The direction is exactly that of the classification target: conjugation
`x ↦ g*x*g⁻¹` carries `P` onto `Q`.

The two cancellation lemmas `comap_iso_hom_inv` and `comap_iso_inv_hom`
follow from `comap_comp` and the inverse identities. `eq_comap_iso_iff`
moves an equality across an isomorphism; `comap_iso_le_comap_iso_iff`
shows that this preimage also reflects inclusion.

Rational conjugacy is proved reflexive, symmetric and transitive. The
reflexive witness is the identity point, and the symmetric witness is the
inverse point. If `g` carries `P` onto `Q` and `h` carries `Q` onto `R`,
the composite witness is `h*g`. The implementation uses
`innerIso_mul_hom` in its published diagrammatic composition order and then
`comap_comp`; this fixes the order without replacing the all-test equality
by a rational-point calculation.

`IsRationallyConjugate.conjugate_iff` identifies the predicates of being
conjugate to a fixed third functor. `existsUnique_index_iff` applies this
pointwise to an arbitrary indexed family. The index type and its uniqueness
are unchanged; no uniqueness of a conjugating point is asserted.

`Dynamic.parabolic_isRationallyConjugate` packages the existing
`Dynamic.parabolic_eq_comap_of_iso` for an actual inner automorphism.
The final two lemmas specialize the index-transport assertion to the exact
subtype of subsets of `simpleRelativeRoots i ν` and the literal
`standardParabolic`/`comap` formula in the classification target.
In particular, conjugating any cocharacter preserves its
unique-standard-index assertion.

These specialized lemmas require only the affineness needed to define the
relative roots. They impose no reductivity, maximal splitness or genericity
hypothesis. They do not assert existence of a standard index for any
cocharacter. They work for empty root systems and the full-group parabolic
without a separate case because their proofs only transport the predicates.
