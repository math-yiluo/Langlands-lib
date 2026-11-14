# Pointwise fixers stabilize sets

For integer-valuation building data `B`, the theorem `IntegerValuationBuildingData.smul_image_eq_of_mem_pointwiseFixer` says that if `g` fixes every point of a subset `Y` of the reduced building, then `(g • ·) '' Y = Y`. Its proof uses the pointwise-fixer membership criterion and proves both inclusions.

This generic lemma is moved unchanged from [UnramifiedSimplyConnectedChamberStabilizerStatement](UnramifiedSimplyConnectedChamberStabilizerStatement.md) for shared use by chamber stabilizers and depth-zero reduction kernels. No simply-connectedness or chamber hypothesis is needed.
