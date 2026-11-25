# Actual original-parabolic conjugation on face-weight vector layers

This internal specialization for the finite vector-bundle filtrations of
supplied relative radicals constructs the actual vector
quotient automorphism induced by a point of the original parabolic, and
proves that it is linear over every coefficient algebra. All abstract
geometric premises of `ParabolicVectorLayerLinearity` are discharged.
There is no supplied quotient-equivariance or quotient-linearity
assumption.

The main constructions assume an arbitrary nontrivial commutative base
ring `R` at universe `u`, an affine actual group scheme `G`, finite split
torus coordinates and root indices, and a supplied
`C : SplitParabolicFaceChart i P fam wt`. The geometric inputs are
`hG : IsReductive G`, fibrewise maximality of the split torus `i`, its
actual fibrewise root datum `P`, and actual root parametrizations `fam`.
The acting point is any base point of `AffineRegularBorel.borel i wt`,
which is the actual represented dynamic parabolic of the original
cocharacter. Despite the historical abbreviation `borel`, the original
cocharacter need not be regular. The auxiliary regular chart and the
positive multiplier realizing its face weights are already part of the
existing construction. The term weights remain the original unscaled
face weights.

`faceScalarAction` restricts the actual root-weight torus action along
`C.faceCocharacter`. `faceScalarAction_comp` proves its actual ambient
conjugation equation on every scheme test, by the two represented
torus-action inclusion equations and the definition of the actual
coordinate cocharacter. `quotientMap_faceScalarAction` proves that the
actual quotient map intertwines this action with the scalar power
`C.faceMultiplier * (d+1)`. It applies the existing actual quotient
equivariance theorem, using `C.facePairing` and `C.weight_eq` to identify
every root pairing with the realization multiplier times the original
weight. Thus the scalar action is proved from the root geometry.

`originalParabolicAction_comp` unfolds the previously constructed
restricted action and proves the actual original-parabolic conjugation
equation. `originalParabolicTermIso` evaluates that actual action at the
given base point. `originalParabolicTermIso_comp` derives its ambient
conjugation equation, including the constant pullback of the point on
every scheme test. `originalParabolicTermIso_step` proves compatibility
of these actual automorphisms with the actual consecutive term inclusion.
The proof cancels the ambient representing monomorphism and uses the
preceding conjugation equations and `comp_step_inclusion`. Neither term
compatibility nor its ambient meaning is a consumer premise.

`originalParabolicQuotientIso` descends these compatible actual term
automorphisms by full fppf quotient uniqueness.
`originalParabolicQuotientIso_fac` identifies its composite with the
actual quotient map as the term automorphism followed by that quotient.
This specifies the actual induced quotient morphism.

`originalParabolicQuotientIso_isEquivariant` specializes the parabolic
linearity argument with
`χ = AffineRegularBorel.cocharacter i C.faceCocharacter`.
`C.isRepresentedBy_faceCocharacter` supplies the exact first-term
representative of its contracting subgroup.
`C.parabolic_faceCocharacter` identifies its actual parabolic with the
original one; the existing full original-parabolic normalization then
supplies normalization of the actual term, and the represented original
parabolic inclusion puts the acting point in this functor. Affineness
supplies separatedness. The preceding actual scalar-action and quotient
equivariance equations supply all remaining geometric premises. The
abstract theorem uses the actual `P=U*Z` limit decomposition and local
fppf quotient lifts, so there is no assumption that the parabolic point
commutes with the face cocharacter.

`originalParabolicQuotientIso_hasScalarWeight` derives the required
all-coefficient-algebra scalar identity from this actual equivariance.
Since `C.faceMultiplier_pos` and `d+1>0` make the scalar power positive,
`originalParabolicLayerLinearEquiv` constructs the linear equivalence of
the actual quotient on every coefficient algebra.
`originalParabolicQuotientIso_eq_matrixHom` identifies its original actual
group-scheme morphism with the morphism of a single base-ring matrix.
This equality therefore applies to every scheme test, including
nonreduced tests. Empty exact-support sets are allowed throughout.

The provenance is internal: this module specializes the existing full
original-parabolic action, actual face-height realization and quotient
equivariance, and the proved parabolic vector-layer linearity adapter.
The only supplied objects are the face chart, the stated geometric
hypotheses, and an actual original-parabolic point. There is no field,
noetherian, reducedness or positive-rank assumption. The nontrivial-ring
hypothesis is retained from the existing actual parabolic comparison.
Different-chart transitions, cover descent, and assembly of the final
relative radical filtration remain separate steps.
