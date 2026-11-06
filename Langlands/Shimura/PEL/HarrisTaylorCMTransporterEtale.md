# Finite-etale geometry of all actual CM transporter maps

This internal development extends the published normal-inclusion result
to every map of the actual represented CM tower. The original arithmetic,
tensor, Picard, duality, polarization, torsion, representability and
rigidity prerequisites remain explicit. It uses the compact open normal
refinement construction and finite-etale source descent of formal
unramifiedness. It does not assert a new literature theorem.

The family `R` consists of the original exact `CMLevelRepresentation`
witnesses, and all scheme maps are the maps of
`representedCMSchemeTower ... R`. The additional named inputs are
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement` and
`DominantUnramifiedEtaleStatement`. For an inclusion, rigidity is required
at its source and target; for arbitrary transporters a rigidity proof at
every small level supplies the needed conjugated-source instance.

`smallCMNormalRefinement D U V` is the actual compact open common
refinement normal in `U`, given its smallness certificate by containment
in `V`. Its two containment laws and normality laws recover the generic
construction. If `V ≤ U`, the same subgroup is normal in `V`.

For an arbitrary inclusion `V ≤ U`, the proof chooses this `W`, and writes
`p : X_W ⟶ X_V` and `f : X_V ⟶ X_U` for the original inclusions. Tower
functoriality identifies `p ≫ f` with the original `W`-to-`U` map.
The normal-inclusion theorem makes both `p` and `p ≫ f` etale.
Projectivity makes `p` finite, and the original dual-geometry surjectivity
theorem makes it surjective on scheme points. The published
`formallyUnramified_of_finiteEtale_comp` then proves formal
unramifiedness of `f`. Openness of the composite normal map descends
through the continuous surjection `p`, by `IsOpenMap.of_comp`.
Smoothness of the original source and target and the supplied dominant
criterion now prove etaleness of the same original `f`.

For a transporter `k : V ⟶ U` with translating element `a`, the actual
conjugated source `a⁻¹ V a` is contained in `U`, by `k.respects`.
`smallCMTransporter_factorization` identifies `k` with the conjugation
isomorphism followed by this identity-element inclusion. The represented
tower preserves this factorization and the isomorphism, so its map at
`k` is etale.

`representedCMFiniteEtaleTransition_of_dominantCriterion` packages this
same original map as an object of `FiniteEtale.Cover X_U`; its finiteness
follows from the published proper-plus-etale transition instance.
`representedCMSchemeTower_map_isFinite_of_dominantCriterion` exposes
that finiteness directly. The `_left` and `_hom` formulas for this cover
are definitional: its source is the original level `X_V` and its
structural map is the original map at `k`.

The `cmSchemeTower_map_etale_of_dominantCriterion`,
`cmSchemeTower_map_isFinite_of_dominantCriterion` and
`cmFiniteEtaleTransition_of_dominantCriterion` constructions specialize
the same results to the exact representation witnesses chosen by the
given `CMRepresentabilityStatement q`. They use the identical choices
that define `cmSchemeTower ... q`. The chosen cover's `_left` and
`_hom` formulas again identify its source and map definitionally.
There is no additional transition-etaleness or finiteness premise.

This pair does not prove representability, existence of a small level,
the dual existence or geometry assertions, rigidity, or the supplied
dominant criterion. It does not extend the tower to nonsmall levels.
