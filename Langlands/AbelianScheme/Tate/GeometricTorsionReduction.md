# Relative specialization for the actual finite torsion rank theorem

This internal derived module proves the comparison and specialization steps
needed by `GeometricTorsionRankStatement`. It does not prove the missing
field-level numerical theorem. Its explicit `FieldTorsionRankStatement` is a
reduction hypothesis about the actual torsion of the actual pulled-back
abelian scheme, not a replacement model or an accepted theorem.

The published additive equivalence `GroupScheme.Tate.levelBaseChange`
comes from the pullback adjunction on actual torsion sections. The new
`levelBaseChangeLinear` preserves the existing `ZMod n` actions by
`ZMod.map_smul`. The isomorphism from the pushed-forward identity test
scheme to the original test scheme gives `levelTestIsoLinear`.
Their composite `fibreTorsionLinearEquiv` compares actual torsion over the
point field with the target's actual torsion sections. No group law is
transported along a bare equivalence of types.

`isUnit_natCast_pullback` maps a global unit through the actual map on global
sections. Composing with `Scheme.ΓSpecIso` gives
`natCast_ne_zero_at_point`. The published
`AbelianScheme.hasRelativeDimension_baseChange` preserves the specified
smooth relative dimension on the pulled-back abelian scheme.

`geometricTorsionRank_of_fieldTorsionRank` applies its explicit field
hypothesis to that abelian scheme, promotes the resulting additive
equivalence to a linear one using the existing residue actions, and
composes with the actual fibre comparison. Finally,
`card_level_of_linearEquiv` calculates the finite function type's
cardinality, using positivity of `n`. These steps cover `n = 1` and
`g = 0` without exceptions.

The reduction implements the relative specialization obligations described
in the paired documentation of the unchanged published
`GeometricTorsionRankStatement`. Its field hypothesis is the algebraically
closed field case of Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(2012-02-08 draft), Chapter V, Corollary (5.11), printed p.75 / PDF p.79,
registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The field multiplication-degree theorem and torsion structure argument
are separated as follows.

`FieldTorsionCardinalityStatement` is the remaining numerical hypothesis:
over every algebraically closed field, actual positive prime-to-characteristic
torsion has cardinality `n^(2*g)`. It is a proposition definition, not an
assertion that the numerical theorem has been proved.
`fieldTorsionRank_of_fieldTorsionCardinality` applies this hypothesis at
every positive divisor of `n`. A divisor is nonzero in the field because
`n` is nonzero there. The proved
`GroupScheme.Tate.levelLinearEquivOfDivisorCard` then constructs the
actual residue-linear coordinates. Thus the algebraic torsion structure
argument is implemented, conditional only on the stated numerical
cardinalities.

`geometricTorsionRank_of_fieldTorsionCardinality` composes this field-level
construction with the proved relative specialization. It derives the
unchanged published target from that explicit field-cardinality
hypothesis. The geometric numerical degree and cardinality theorem
remains unproved in this module; the conditional theorem does not
complete the geometric rank proof task.
