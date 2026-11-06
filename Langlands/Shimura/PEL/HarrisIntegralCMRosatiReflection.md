# Reflecting rational Harris Rosati compatibility

This internal comparison reflects the existing rational Rosati equations into
actual equations for a supplied integral action on the same abelian scheme.
It retains the positive auxiliary left involution and the original rational
extension of the actual Harris order action. The general reflection lemmas
allow an independent scheme universe; arithmetic types have universe zero.

For a supplied abelian scheme, its chosen dual, tensor and Picard prerequisites,
dual additivity, inverse Poincare bundle, evaluation and dual geometry, assume
every positive integer is a unit in the base's global sections.
`rationalRosatiBasisEquations_iff_integral` compares the existing rational and
integral finite-basis equations for an actual map to this chosen dual. The
reverse implication is the published rationalization lemma. For the forward
implication, rational dualization and composition on actual maps are their
actual counterparts followed by rationalization. The published
`Tate.ofHom_injective` then reflects each equality. No geometric point,
connectedness, torsion finiteness or Tate-image hypothesis is needed.

`rationalAction_involutionCompatible_iff_integralBasis` combines reflection
with the existing rational basis criterion.
`rationalAction_involutionCompatible_iff_integral` also uses the existing
integer-basis criterion, with the explicit dual-additivity premise, to obtain
every actual order equation.

For the CM specialization, fix the original normalized Harris charts, the
named prerequisite package, an actual family `B/S`, its `DualWitness W`, an
actual map `lam` to its dual and a structural morphism `p : S → Spec F`.
For every quasi-separated test `T` over `S`, use the same direct pullback
family, canonical pulled-back dual witness and canonical pulled-back map.
The already published `cmBaseTorsionUnit` derives invertibility of all
positive integers from `T.hom ≫ p`; it is not an additional premise.
Published relative dual additivity applies on this test.

`harrisIntegralActionFullRosatiCondition_iff_involutionCompatible` therefore
identifies all actual order equations with the original rational involution
compatibility. `harrisIntegralCMFullActionCondition_iff_involutionCompatible`
adjoins exactly the unchanged normalized rational Lie determinant condition.
The suffix `_iff_rationalUnitMultiple` replaces the rationalized map by any
nonzero rational unit multiple using the existing scalar-invariance theorem.
No map, integral action, determinant coefficient or family is changed.

For the existing closed action locus, retain the locally noetherian base and
the supplied relative-End representative with its separated, locally finite
type geometry and natural comparison on all locally noetherian tests.
`harrisIntegralCMClosedActionLocus_factors_iff_involutionCompatible`
strengthens its existing factorization criterion to an equivalence with the
original rational involution compatibility and normalized determinant on
the actual classified integral action. The suffix
`_factors_iff_rationalUnitMultiple` gives the same equivalence for every
nonzero rational multiple of the canonical pulled-back map.
Both proofs combine the existing full-order factorization criterion with
the reflection just proved.

`harrisIntegralCMClosedActionLocus_existsUnique_iff_involutionCompatible`
gives a direct universal property for any supplied actual integral action.
Its rational compatibility and determinant hold if and only if there is a
unique actual morphism to that existing closed locus whose restriction of
the actual universal action is exactly the supplied action. In one direction
the existing full-action classification supplies its condition. Conversely,
reflection supplies that condition and the inverse of the existing
classification supplies a morphism. Its literal value formula gives the
required equality, and injectivity proves uniqueness. Thus the result
classifies the same actions on the same direct family by actual scheme
morphisms. It introduces no new quotient, test category, action functor
or representing scheme.

`harrisIntegralCMClosedActionLocusRationalLift` constructs this unique
actual morphism from the supplied action and exactly its rational
compatibility and determinant. It applies the inverse existing full-action
classification after reflection. The suffix `_apply` proves the literal
restriction formula, and `_eq` identifies every other actual morphism
with that formula with this constructed lift. These are actual morphisms
in `Over S`, not new representatives of an equivalence class.

The provenance is internal: the published injectivity of actual Hom
rationalization, the finite rational and integral basis criteria, structural
invertibility of integers and scalar invariance supply all deductions.
The fixed family, its dual witness and map, and the relative-End
representative remain supplied data. This work does not construct an
integral action from an arbitrary rational action, a polarization, an
ambient ordinary moduli scheme, a representing scheme for the original
CM presheaf, or its geometric properties. The protected
`DivisionCMRepresentabilityStatement` and all imported Lean/Markdown pairs
are preserved; its existence and output admissibility obligations remain open.
