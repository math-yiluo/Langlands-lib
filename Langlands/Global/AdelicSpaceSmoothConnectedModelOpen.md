# Smooth connected maps on actual adelic levels

This derived unit assumes the exact `SpaceUniformLangWeilStatement` and
specializes `SmoothDimensionUniformLifts` to actual rings of S-integers. Both
spaces are separated and finite type. Their map is smooth with nonempty
geometrically connected fibres; its relative dimension need not be constant.
The S-integer ring has a specified algebra structure over the lifted integers,
whose spectrum map is locally of finite type.

For each global-field characteristic, the proved S-integer Noetherianity
allows the uniform Henselian surjectivity theorem to apply. Its one positive
constant is chosen before the place. The published finiteness of places with
bounded residue-field cardinality makes the places whose residue cardinality
is at most its square a finite set. Outside that set, the actual complete
valuation ring is Henselian and its actual residue field is finite. Applying
the uniform theorem to the canonical surjective residue algebra map proves
surjectivity of the original coefficient-ring point map.

The curve-place exceptional set also contains the finite set of places in S.
The number-field exceptional set additionally contains all infinite places.
This is an exception to the surjectivity assertion only: the factor index and
the level topology retain every infinite factor. `cofiniteSpacePointLifts`
chooses actual preimages outside the finite exceptional set.

The level-openness theorems combine this cofinite surjectivity with the
published `completeFieldSmoothSpacePointOpen` theorem and the actual
coordinate-product topology reduction. Local openness is used at every
factor, including every infinite number-field place. Curve-place level
openness requires S to be nonempty.

All provenance is internal: uniform lifting across the actual finite dimension
strata, residue-cardinality finiteness, complete-valuation-ring Henselianity,
and the coordinate openness reduction. The Lang–Weil premise remains explicit;
this unit does not prove the unconditional adelic smooth-openness statement.
