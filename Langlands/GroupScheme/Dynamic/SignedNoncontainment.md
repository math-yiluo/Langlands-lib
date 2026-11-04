# A dynamic direction outside a proper smooth closed subgroup

This internal result works over every field in universe `u`, in every
characteristic. The ambient group `G` is smooth, connected and affine.
The subgroup `b : B ⟶ G` is an actual closed inclusion, with `B` smooth
and affine. A split torus maps to `G`, and `ν` is one of its cocharacters.
No reductivity or maximality is required.

`RelativeRoot.sup_signed_dynamic_tangentSubmodules` proves that the
intrinsic tangent submodules of the positive dynamic identity-limit group,
the dynamic centralizer, and the negative dynamic identity-limit group
span the whole actual Lie algebra. The proof uses the published exact
identification with the positive, zero and negative weight spans. Every
integral pairing is positive, zero or negative, so each torus weight space
belongs to one of those three spans. The split-torus internal weight
decomposition proves that these spaces span the whole Lie algebra.

`Dynamic.isIso_of_signed_dynamic_le_range` assumes that all three
dynamic subgroup functors lie in the range of `b`, on every relative
scheme test. Their tangent images therefore lie in the image of the
actual differential of `b`. The spanning equality makes this differential
surjective. The existing smooth closed subgroup equality theorem then
proves that this actual inclusion is an isomorphism. Smoothness and
closedness of the specified inclusion are essential to this step.

Consequently, if `b` is proper and contains the dynamic centralizer, at
least one of the positive and negative dynamic identity-limit subgroups
is not contained in its range. `NoncontainedSignedDirection` stores
the selected actual cocharacter, its equality with `ν` or `-ν`, and
this all-test noncontainment. `noncontainedSignedDirection` makes the
choice by testing the positive sign and otherwise taking the negative one.

This is a composition of existing Library tangent and subgroup equality
results, rather than a translation of a new external theorem. It supplies
a noncontainment input for the homogeneous-curve argument. The properness
of `b`, the centralizer containment and the quotient curve remain separate
obligations; no rank-one positive-root uniqueness theorem is claimed here.
