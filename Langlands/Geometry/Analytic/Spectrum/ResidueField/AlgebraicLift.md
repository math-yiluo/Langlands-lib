# Lifting a prescribed character along an algebraic residue extension

This internal helper performs the affine character-extension step for a bounded
map `f : A → B` of normed commutative algebras over an ultrametric normed field
`K`. The fields, both algebras, and the target field have independent universes.
It assumes algebraicity of the completed residue extension at the chosen
spectrum point; it does not prove this geometric input for étale maps.

For `y : BanachSpectrum B`, put `x = BanachSpectrum.comap f y`.
`IsAlgebraicCompletedResidueComap K f y` means that the actual field
`CompletedResidueField K y` is algebraic over `CompletedResidueField K x`,
with the scalar action induced by the canonical isometric map
`completedResidueComap K f y`. This is a proposition definition about the
published completed residue fields, not an assumed instance.

Let `L` be a complete, algebraically closed ultrametric normed field which is
a `K`-algebra. If `g : A →ₐ[K] L` is a prescribed character with
`‖g a‖ = x a`, the theorem
`exists_character_lift_of_isAlgebraic_completedResidueComap` constructs a
bounded `K`-algebra character `h : B → L` such that `‖h b‖ = y b` and
`h (f a) = g a`.

The proof extends `g` to an isometric embedding of the completed residue field
at `x`, using `completedResidueLift`. The canonical map between the completed
residue fields induces a normed algebra structure and a compatible `K` scalar
tower. Its assumed algebraicity permits application of
`exists_isometric_algebraic_extension` from
`Langlands.Geometry.Analytic.ValuedField.AlgebraicEmbedding`. Composing that
extension with the completed residue evaluation at `y` gives `h`. Isometry
and `norm_completedResidueMap` prove its norm identity. The two published
evaluation identities, `completedResidueComap_map` and
`completedResidueLift_map`, prove that its restriction equals the prescribed
`g` exactly.

All results are deductions from the imported Library constructions and Mathlib;
no additional literature assertion is used. The ground field need not be
complete or nontrivially normed. The module does not supply algebraicity,
chart independence, gluing of characters over an atlas, or lifting in the
localized analytic category.
