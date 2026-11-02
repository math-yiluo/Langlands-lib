# Multiplication on a smooth actual torsion closure

The lemma `Langlands.AbelianScheme.Tate.exists_mul_on_smooth_twoPowerTorsionClosure`
constructs multiplication on a specified smooth closed immersion whose
image is the actual two-power torsion closure, over any algebraically closed
field in universe `u`. Its multiplication is a morphism over the field
compatible with the ambient abelian scheme's multiplication.

The fibre square of the smooth scheme over the field is smooth, hence reduced,
and is a Jacobson scheme. Each of its closed points is represented by a rational
section. The two projected sections of the ambient abelian scheme lie in the
actual closure, so their product lies there by the published section-subgroup
theorem. The inverse image of the closure under the ambient multiplication is
closed and contains all closed points, hence is the whole fibre square.

The public helper `exists_factor_closedImmersion_of_reduced` shows that a
morphism from a reduced scheme whose range lies in a closed subscheme factors
through that closed immersion: its base change is a surjective closed immersion
into the reduced source and is therefore an isomorphism. Applying this
factorization gives the required multiplication morphism.

This is an internal geometric derivation from the actual closure-section
subgroup, closed points over an algebraically closed field, and Mathlib's
reduced-source closed-immersion theorem. The companion group-scheme proof
supplies the smooth closed realization and descends the group laws. This
lemma assumes no characteristic restriction and proves no connectedness,
dimension comparison, numerical torsion count, or torsion density.
