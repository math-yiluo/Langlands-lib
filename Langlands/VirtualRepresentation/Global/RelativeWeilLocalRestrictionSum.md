# The restriction formula for induced relative Weil representations

Lean module: `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionSum`.

The theorem `continuousRestrict_continuousInduceAlong_restrictionInclusion` proves condition 2 of
`Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestriction` for the local maps
`localPlaceMap`: for `ι : W_{F_z} →ₜ* W_{E/F}` (discrete topology on `Gal(E/F)`) with
`j_w(projection (ι g) x) = localProjection g (j_w x)`, the restriction along `ι` of the
induction from `W_{E/K}` of a continuous virtual representation `x` is
`∑_u continuousInduceAlong (completionWeilMap z u) (continuousRestrict (localPlaceMap u) x)`.

The proof applies Mackey's formula
`ExactGrothendieckGroup.continuousRestrict_continuousInduceAlong`
(module `Langlands.VirtualRepresentation.ExactMackeyAlong`, by Worker 1828) with
`j = restrictionInclusion c F E K h`, `φ u = completionWeilMap z u`, representatives
`placeRepresentative`, and the double-coset facts `restrictionInclusion_localPlaceMap`,
`conj_mem_range_restrictionInclusion_iff`, `exists_eq_mul` and `place_eq_of_mul_eq` from
`Langlands.ClassField.Global.RelativeWeilLocalCosets`. Compare Tate (1979), (2.3.5).
