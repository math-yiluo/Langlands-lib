# Full ordinary derivatives of quasi-split integer apartments

`Langlands.Geometry.Building.quasiSplitDerivativeAffineRoots` proves the
exact Library proposition `QuasiSplitDerivativeAffineRootsStatement` at
every universe `u`. It retains the prescribed maximal split torus, the
arbitrary supplied apartment and centralizer, and all the statement's
original hypotheses. The conclusion concerns ordinary affine roots
and includes all multipliable and doubled relative-root directions.

The proof equips the field with the valuative relation induced by its
given integer-valued valuation. The theorem
`quasiSplitAllDepthBoundedApartmentExistence` constructs a full-V6
apartment for this same maximal split torus with algebraically bounded
root filtrations at every point and depth. Its centralizer
representation may differ from the supplied one.
`IntegerValuation.IsOmegaCompatible.of_centralizerDatum` transfers its
compatibility to the supplied centralizer. Then
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` identifies
the constructed apartment with the supplied apartment.

The resulting `IntegerValuationBuildingData` therefore has a bounded
filtration for each actual relative root, obtained by choosing any
apartment point and depth zero. Surjectivity of the valuation supplies
an element with value `WithZero.exp (1 : ℤ)`, hence an element strictly
larger than one in the induced valuative relation. The theorem
`IntegerValuationBuildingData.derivativeRoots_affineRoots_of_bounded`
now proves the required equality. Its multipliable-root argument uses
the actual vector quotient of the root group by its doubled-root
group and algebraic boundedness; its other branch uses a strict
filtration jump. These arguments apply in every field and residue
characteristic.

This is an internal composition of the named Library interfaces and
the supporting bounded-filtration theorem. It uses the bounded
quasi-split apartment construction and uniqueness instead of computing
canonical jump sets explicitly. No additional premise about boundedness,
completeness, topology, reducedness or absolute maximality is imposed
on the target.
