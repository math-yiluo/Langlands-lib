# Lifting through a reduction preimage

This module constructs `RelativeComponentModelHom.reductionPreimageLift` and
proves a criterion for the reduction-preimage clause of KP facet-model axioms.
It works at arbitrary universe `u` for the actual affine integral models and
schematic images already defined in the Library.

The content is derived infrastructure: it uses the published model-map
naturality, schematic-image factorization, smooth Henselian reduction and
Mathlib's subgroup map/comap identity. It does not assert a new result from an
external source. In particular, it does not prove
`UnramifiedFacetParabolicImageStatement`: both geometric inputs below must
still be established for the characterized facet models.

All declarations are in
`Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom`. Fix a
commutative local domain `R`, its fraction field `K`, a group scheme `G/K`,
relative-component pairs `source` and `target`, and an identity-generic-fibre
morphism `φ : RelativeComponentModelHom source target`. Each pair carries
smooth full and neutral models and connected neutral fibres through
`RelativeComponentModelData`. Write `f` for the map
of neutral integral sections, `r` for the target reduction, `b` for the neutral
special-fibre map, and `π` for its projection onto its schematic image. These
are the actual Library maps. The residue-point subgroup `P` is
`φ.specialFibreImagePoints`, the range on residue-field points of the image's
closed inclusion, rather than a presumed range of `b`.

The local instances supply affineness of the neutral special fibres and their
underlying schemes from the affine models and stability under base change.
They also allow quasi-compactness of the special-fibre homomorphism to be
inferred when forming the image projection.

For any local `R`:

- `sectionRange_le_reductionPreimage` proves `range(f) ≤ r⁻¹(P)` using reduction
  naturality and `SchematicImage.projection_inclusion`. Its proof uses neither
  the carried smoothness nor a rational-surjectivity hypothesis.
- `specialFibreImagePoints_eq_range` proves `P = range(b)` under the explicit
  hypothesis that `π` is surjective on points over the original residue field.
  It lifts each image point through `π` and uses the same factorization in
  both directions.
- `congruenceKernel_le_sectionRange_iff` identifies
  `target.neutral.congruenceKernel ≤ range(f)` with
  `target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints`.
  The forward implication takes generic points of a section lift. The reverse
  implication lifts the generic point in the source and uses injectivity of
  `target.neutral.integralPointMap` to recover equality of integral sections.

Now assume `R` is Henselian. The following declarations take an explicit
source-smoothness argument, which can always be supplied by
`source.neutral_smooth`:

- `sectionRange_map_reduction` proves `r(range(f)) = range(b)`. One direction
  is naturality; the other lifts a source residue point using
  `IntegralModel.reduction_surjective`.
- `reductionPreimage_eq_sup_congruenceKernel` assumes the same rational
  surjectivity of `π` and proves
  `r⁻¹(P) = range(f) ⊔ target.neutral.congruenceKernel`. It substitutes the
  preceding two range equalities into `Subgroup.comap_map_eq`.
- `hasParabolicReductionPreimage_iff` consequently proves
  `φ.HasParabolicReductionPreimage ↔
  target.neutral.congruenceKernel ≤ range(f)`, by `sup_eq_left`.

Under the explicit source-smoothness argument, rational surjectivity of `π`,
and generic-point containment
`target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints`, the
noncomputable definition `reductionPreimageLift` chooses a source integral
section for each element of `φ.specialFibreImagePoints.comap r`. The preceding
criterion supplies its existence. `reductionPreimageLift_spec` states that
applying `f` returns the given target section, by `Classical.choose_spec`.
No homomorphism property is asserted for this chosen lift.

The proofs do not use target smoothness, but the formal interface still carries
it through `target : RelativeComponentModelData R K G`. No parabolicity,
finite-residue-field hypothesis, split-unipotent-kernel hypothesis or rational
surjectivity conclusion is implicit: rational surjectivity of `π` and
containment of the target congruence subgroup are explicit inputs to the lifting
construction and the preimage criterion.
