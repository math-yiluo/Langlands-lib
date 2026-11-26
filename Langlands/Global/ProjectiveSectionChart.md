# Algebraic sections on projective affine charts

`Langlands.Global.ProjectiveSectionChart` records a section of a specified map
over a basic open in the preimage of a standard projective coordinate chart.
The section equation uses the actual open subscheme inclusion. The preimage
of a chart under a closed immersion is affine because its restriction to the
affine chart is again a closed immersion.

The finite-cover theorem starts with sections around all rational points of
a Noetherian quotient. At a rational point it chooses a standard chart
containing the projective image. Basic opens of the affine chart preimage
give a smaller neighborhood inside the section's original domain. The proof
restricts the section to that basic open. The set of closed-point images of
rational points is compact in the Noetherian topology, so finitely many such
open domains cover it.

`exists_finite_cover_of_openImmersion` applies the same construction to the
rational image of an open immersion. Its local section is the inverse
of the isomorphism onto the open image, so every section in the finite
cover takes values in the source of the open immersion.

Over a number field, let the rational points in one such domain have supplied
homogeneous coordinate vectors. A regular function on the affine target of
the section pulls back to the localization at the basic-open element. The
closed immersion makes the projective chart algebra surject onto the
coordinate algebra of its preimage. The values of the standard chart ratios
are the coordinate ratios of the supplied vectors. To see this, the proof
compares vanishing of the linear form `X_i - r_i X_j` at the chart point and
at the supplied vector, where `r_i` is the value of the chart ratio. This
gives `r_i a_j = a_i` for every `i` and forces `a_j ≠ 0` because the vector is
nonzero. Each ratio has scalar height at most the homogeneous vector
height. The height-bounded subalgebra and localization lemmas then give one
polynomial bound for the regular function across the domain.

This internal construction combines the Library's normalized projective
coordinate and actual point-lifting APIs with Mathlib's affine basic opens,
closed immersions, localization, and Noetherian compactness.
