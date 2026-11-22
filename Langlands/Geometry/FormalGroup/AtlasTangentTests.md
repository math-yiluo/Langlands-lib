# Tangent vectors on chart tests

An affine test algebra of a formal atlas can be followed by any further coefficient map. If a chart generator becomes invertible, the universal principal localization gives a unique map into the new test. `BasicAtlas.tangentTestEvaluation` uses that map on the corresponding component of a compatible tangent vector. The overlap equation and coefficient naturality of the derivative make different chart evaluations agree under the actual transition whenever both chart generators are invertible.

`BasicAtlas.tangentMap` extends the compatible tangent module along a map of affine test algebras by these chartwise evaluations. It is semilinear over the test coefficient map, preserves identities and composition, and evaluates after extension by evaluating on the composite test. For an atlas with a full order action the map intertwines the original order endomorphisms.

This is the coefficient functoriality of the compatible chart tangent modules underlying Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B, printed p. 110 (PDF p. 4).
