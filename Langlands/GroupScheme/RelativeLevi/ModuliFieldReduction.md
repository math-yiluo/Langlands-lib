# Reducing the Levi presheaf to a field-extension assertion

This internal reduction connects the precise missing field assertion to the
actual Levi-image presheaf. Its parameter `hfield` asserts that for an arbitrary
extension of algebraically closed fields in universe `u`, the actual pullback
of a supplied `IsUnipotentRadical` in a smooth ambient group again satisfies
that unchanged predicate. The extension may be transcendental, and the ambient
need not be affine or connected. This is an explicit hypothesis, not a
proved theorem or a replacement definition of a radical.

`IsRelativeUnipotentRadical.baseChange_of_smooth_field_extension` starts with a
relative radical in a smooth ambient group. For each point of the new base,
the compatible embedding of the chosen residue-field algebraic closures is
given its induced algebra structure. The structure morphism of the old
geometric fibre is smooth by pullback. Applying `hfield` to that fibre gives
exactly the extension assertion required by
`IsRelativeUnipotentRadical.baseChange_of_geometric_extension`. That existing
lemma supplies the actual geometric-fibre comparison as well as closedness,
smoothness and normality of the pulled-back radical.

`IsRelativeLeviSubgroup.baseChange_of_field_extension` uses the actual
Levi-times-radical multiplication isomorphism to obtain ambient smoothness
from `IsRelativeLeviSubgroup.smooth_ambient`. The preceding radical result
then discharges the explicit preservation premise of
`IsRelativeLeviSubgroup.baseChange_of_radical_preservation`. No independent
smoothness or affineness premise on the original ambient is added.

`RelativeLevi.restrictionStable_of_field_extension` takes an actual presenting
relative Levi inclusion for a moduli value over a test scheme. It pulls that
inclusion back along the restriction morphism and postcomposes by the
existing ambient pullback comparison. Relative-Levi transport through that
isomorphism and `restrictImage_range` identify its all-test image with the
existing literal subgroup restriction. This proves `RestrictionStable P`
for every ambient `P`, still conditional on `hfield`.

`RelativeLevi.moduliFunctorOfFieldExtension` applies the existing
`moduliFunctorOfStability` to this proof. Its values are the actual Levi
subgroup images of the actual pullbacks, with equality of subgroup functors
and the already proved identity and composition laws. The conjugation
action and its restriction compatibility are those of
`leviConjugationAction` and `LeviImage.restrict_smul`, specialized to the
derived stability proof. All schemes stay in universe `u` and the value
type is `Type (u+1)`.

The provenance is the implemented composition of the existing closure
embedding, geometric-fibre comparison, smooth pullback, multiplication
transport, relative-Levi isomorphism transport and actual subgroup
restriction APIs. No original-source claim about the broader field
assertion is made here. Its justification and proof remain separate
obligations; until they are supplied, this module does not provide the
unconditional moduli functor, representability, a torsor, or a global Levi.
