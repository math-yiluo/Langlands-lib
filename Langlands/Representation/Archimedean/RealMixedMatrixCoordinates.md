# Real matrix coordinates from the rational mixed archimedean space

This internal comparison specializes the mixed matrix models of [ArchimedeanGL](../../Global/ArchimedeanGL.md). Its purpose is to reuse differential and analytic results on those models on the actual real general linear group.

The rationals have one infinite place, which is real. `rationalMixedSpaceEquiv` evaluates the real function component at this place. Its inverse sends a real scalar to the constant function in the real component and the zero function in the empty complex component. Uniqueness of the real place and emptiness of the complex-place index prove the inverse identities. Evaluation is a real algebra equivalence and respects the star operation (the target star is trivial).

`rationalMixedMatrixEquiv` applies this equivalence to every entry, respecting the algebra and matrix star operations. `rationalMixedMatrixCLE` is the same map as a continuous real linear equivalence, using finite-dimensionality and the original matrix norm topologies. `rationalMixedUnitsEquiv` maps units through the algebra equivalence; the value lemmas identify the underlying matrices in both directions. The smoothness lemmas reduce each direction to its continuous linear map composed with the open units chart. Thus the comparison does not replace invertible matrices or their real manifold structures by an algebraic model with a different topology.

No result about the analyticity of representation coefficients, irreducibility, or inverse-transpose pairing is asserted in this file.
