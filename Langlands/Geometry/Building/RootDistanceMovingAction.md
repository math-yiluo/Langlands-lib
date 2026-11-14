# Root-distance preservation by moving-apartment actions

This internal bridge combines `ApartmentQuotientRootDistance` with
`ApartmentQuotientMovingSemilinearAction` on the original supplied
`KPApartmentData` quotient. The field and the coefficient group have arbitrary
universes. The reference torus is maximal split in a connected reductive
group, the actual relative roots have a finite type, and common apartments
are explicit premises.

The moving action data include its actual group correction and corrected
apartment maps, with the normalizer and sharp-fixer compatibilities and
normalizer defects already required for the published coherent quotient
action. The additional hypothesis here says that each corrected apartment
map preserves the canonical root norm of every affine displacement. No
existence of such coefficient data is asserted.

`movingAction_smul_apartmentMap` records the action on a translated chart:
the translated coordinate becomes the corrected apartment coordinate and
the translating rational point becomes its coefficient image times the
correction. For any two quotient points, choose one common apartment.
Apply this formula to both points and use the intrinsic distance's
translated chart formula on the source and target. The norm-preservation
hypothesis then proves `chosenRootDistance_movingAction`.

Once a pseudometric realizes that same intrinsic distance,
`movingAction_isometry` follows from equality of distances.
`movingActionIsometryEquiv` bundles the existing quotient permutation as an
isometric equivalence; its underlying map is unchanged. These results
require no separate scalar-isometry premise, since the translated chart
formula already treats every rational translate.

The provenance is solely the two existing internal constructions and their
proved chart and action formulas. This unit supplies no triangle
inequality, retractions, completeness, curvature, actual coefficient
transport, or finite-orbit theorem. Those remain obligations when assembling
the complete unramified metric-action target.
