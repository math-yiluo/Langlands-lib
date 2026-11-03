# Affine coordinate smoothness and the closed subgroup bridge

This is an internal transport helper by Worker 1345 for
`Langlands.GroupScheme.Diagonalizable.FixedSubgroupSmoothStatement`.
It derives the needed facts from the published affine coordinate presentation
and Mathlib's scheme and ring smoothness criteria; it asserts no new result
about how fixed points give formal smoothness.

For a group scheme `G` over `Spec R` with affine structure map,
`coordinateAlgebra_smooth` proves that scheme smoothness of `G` implies
`Algebra.Smooth R (Lie.coordinateAlgebra G)`.
`smooth_of_coordinateAlgebra_smooth` proves the reverse implication.
Both results use `Lie.coordinateIso` to identify the original scheme over
`Spec R` with the relative spectrum of the chosen algebra. They then apply
`HasRingHomProperty.Spec_iff` for smoothness and `RingHom.smooth_algebraMap`.
The forward proof composes the coordinate isomorphism with the original
structure map. The reverse proof composes its inverse with the spectrum's
structure map. `Over.w` identifies these composites with the desired maps.

`smooth_of_formallySmooth` considers group schemes `C` and `G` over a field `k`
and a group-scheme morphism `j : C ⟶ G`. It assumes that `j` is a closed
immersion on underlying schemes, that `G` is smooth and affine over `k`, and
that `C` is affine over `k`. Its explicit remaining hypothesis is
`Algebra.FormallySmooth k (Lie.coordinateAlgebra C)`; its conclusion is
`Smooth C.X.hom`.

The closed immersion is locally of finite type. Composing it with the smooth
ambient structure map makes `C` locally of finite type over the field.
`Lie.coordinateAlgebraFiniteType` therefore makes its coordinate algebra finite
type over `k`. Since a field is noetherian, this gives finite presentation.
Together with the supplied formal smoothness, it gives algebraic smoothness.
The reverse coordinate criterion transports this to scheme smoothness of `C`.

The module does not prove affineness of `C`, extract a diagonalizable coaction,
or supply the formal smoothness hypothesis. Those are separate steps in the
fixed-subgroup proof. It works uniformly in the universe `u` and imposes no
condition on a diagonalizable actor or its characteristic torsion.

`SmoothOfFormallySmoothStatement` is the explicit internal proposition universally
quantifying the field, the two group schemes, the closed immersion and the
affineness and ambient smoothness hypotheses described above. The theorem
`smoothOfFormallySmoothStatement` proves exactly that proposition by applying
`smooth_of_formallySmooth`. These declarations package the bridge without
changing its hypotheses. The declaration is an internal prerequisite statement,
and is separate from the exact diagonalizable fixed-subgroup target.
