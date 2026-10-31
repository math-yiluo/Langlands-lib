# Determinant-compatible pointed Harris polarized pullback

This internal construction restricts the actual representative and ambient
polarized-isogeny quotient pullbacks of `HarrisPolarizedClassBaseChange` to
the existing Harris rational Lie-determinant classes, using exactly the
constructed pulled-back action and the composite reflex-field structure map.

`levelDataBaseChange_objectCondition` applies the generic all-chart theorem
`harrisRationalLieDeterminantCondition_baseChange_of_naturality` to the source
abelian scheme and rational action. The action inside `levelDataBaseChange`
is definitionally that actual base change, so the conclusion is the existing
`PositiveObjectCondition` on the constructed target representative. The named
`LieBaseChangeNaturalityStatement S` remains an explicit hypothesis.

`ambientClassBaseChange_condition` proves preservation of the existing
quotient predicate by quotient induction and that representative theorem.
`harrisClassBaseChange` restricts the constructed ambient map to the existing
`HarrisIsoClass` subtype. Its value on an actual satisfying representative
is precisely the class of `levelDataBaseChange` with the proved determinant
condition. `harrisClassTowerBaseChange` inherits naturality at every original
Harris compact-open transporter arrow from the ambient natural transformation,
using injectivity of the subtype inclusion. The final inclusion square states
that this restriction commutes with the existing natural ambient inclusion.

All named tensor, Picard, dual-naturality and polarization-stability inputs,
the constrained family of dual construction data, finite-fibre and torsion
hypotheses, adelic comparison, ordered-pair additivity and pointed geometric
base-change data remain as in the ambient construction. There is no flatness
assumption on the base map. No numerical-dimension condition, normalized CM
comparison, successive-base-change coherence, unpointed moduli presheaf,
scheme representability, canonical model or coefficient descent is asserted.

The provenance is an internal derivation from the imported actual pullback
constructions, the existing all-chart rational determinant pullback theorem,
and the quotient and subtype universal properties. The imported Harris
definitions retain their original-source conventions and citations; this
module makes no new original-literature claim.
