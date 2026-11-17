# A maximal split torus whose unramified units fix the prescribed point

This module proves the exact published
`Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement.{u}`.
The original nonarchimedean local field, connected reductive group, supplied
maximal-unramified building and coefficient-fixed point retain their original
hypotheses. The conclusion is a maximal split torus over the original field
whose unit subgroup over the maximal unramified field fixes that very point.
The proof is in arbitrary universe and both characteristics.

The proof first applies `unramifiedSpecialReferenceApartment` to obtain a
genuine descended special apartment containing a maximal split torus over the
original field. Its building comparison is equivariant for the same full
ambient rational-point group; it supplies a coefficient-fixed point mapping to
the prescribed original point. The reference torus is used to construct an
integral split source, rather than asserted to fix this point already.

In that special apartment, `unramifiedSpecialApartmentChamber` constructs a
regular ordinary facet invariant under coefficient automorphisms.
`KPApartmentData.unramifiedStableChamberResidue` retains its literal image as
an original maximal Galois facet. It supplies actual compatible lower and
upper component-model recovery and a valid reductive quotient with no proper
rational parabolic inclusions. The published full-facet integral-point
identity packages this same facet recovery as `RecoveredApartmentFixerModels`.
Its `exists_integralSplitSource` theorem constructs one integral split source
with both a maximal generic map and a maximal residue map into that same
reference quotient.

Choose a coefficient-fixed point in this reference facet. Together with the
prescribed reference-building point it gives a fixed pair.
`exists_recoveredFixedBuildingPairZeroModels` constructs actual compatible
pair models with both exact fixer identities. The full integral points are
the character-valuation kernel intersected with the pair fixer; the neutral
integral points are the zero subgroup intersected with that same fixer.
`unramifiedPairFacetSplitSource` then constructs the neutral-model comparison
to the reference facet and lifts the prescribed split residue source into the
pair model. It supplies maximality of the generic torus and fixation of the
prescribed reference point by every unramified unit. Its comparison uses zero
no inversions, rather than an equality of full point and full facet fixers.
Finally `IsFixedByScalarTorusUnits.map` transports this unit fixation through
the same-group equivariant building comparison, whose chosen point maps
exactly to the original prescribed point.

The published Library inputs used directly here are
`unramifiedSpecialReferenceApartment` from
`UnramifiedSpecialReferenceApartment`, `unramifiedSpecialApartmentChamber`
from `UnramifiedSpecialApartmentChamberProof`,
`RecoveredApartmentFixerModels.exists_integralSplitSource` from
`UnramifiedRecoveredSplitSource`, both
`unramifiedIntegerFacetModels_full_integralPoints` and
`unramifiedIntegerFacetModels_neutral_integralPoints` from
`UnramifiedIntegerFacetModels`, and `IsFixedByScalarTorusUnits.map` from
`TorusUnitFixationTransport`. The supporting stable-chamber adapter composes
the published fixed-centroid, facet-incidence and
`constructedMaximalGaloisFacetResidue` theorems to retain the literal ordinary
facet. The supporting pair construction uses the published
`MaximalUnramified.commonApartments`, `unramifiedParahoricModel` and
`exists_recovery_of_fixedBuildingSubset`. The supporting pair-to-facet lift
uses the published `MaximalUnramified.zeroFacetNoInversions`,
`UnramifiedComponentModelRecovery.nonempty_neutralHom_iff`,
`IntegralModel.unramifiedSmoothHomExtension`,
`isMaximalTorus_specialFibreMap_of_unramified_full_pair`,
`IsMaximalTorus.comp_of_perfect_field_unipotent_kernel`, and
`IntegralModel.exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits`.
Their paired Markdown explains those implemented model, residue and lifting
steps. The support files included with this proof retain these actual
constructions, including the exact compatible maps, rather than assuming
existence of the final torus. This proof does not use the Galois-fixed-building-point or building
descent statements excluded by the task. Neither the target statement nor any
of its imported Lean/Markdown pairs is changed.

For combined imports with `UnramifiedTorusUnitFixedApartmentProof`, the
eight local arithmetic instances now have explicit names beginning with
`fixedPointSplitTorus`. This avoids collisions between Lean-generated
declaration names in the two proof dependencies. Their types and implementations and all mathematical statements are
unchanged.
