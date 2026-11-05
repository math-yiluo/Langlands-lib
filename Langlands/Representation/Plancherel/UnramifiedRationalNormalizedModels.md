# Normalized universal models on actual rational points

Worker 16. This derived application uses the literal point subgroups and full
rational-character norm family of `ParabolicPointIntertwiningRegion`, together
with `UnramifiedNormalizedModels` and `UnramifiedNormalizedTensorModels`.
The source motivation is Waldspurger 2003 I.5 (printed p.245) and IV.1
(printed p.277), registered as `waldspurger-2003-plancherel`.

`ParabolicPoints p` and `UnipotentPoints n` are precisely the ranges at the
identity test scheme of p and n followed by p. The Levi is the existing
`parabolicLeviPointSubgroup p l`. `RegularAlgebra r` uses every member of
`parabolicLeviRationalNormCharacters r`, indexed by all rational characters
of the Levi scheme. Its carrier is the existing concrete evaluation-generated
subalgebra, without a finite norm-family choice.

`isOpen_commonNormKernel` obtains local compactness of the actual Levi from
its proved closedness in the locally compact ambient point group.
It then applies `commonNormKernelTopology` to the entire continuous rational
norm family. `isSmooth_universalRepresentation` applies this openness and
smoothness of the complex coefficient action to the actual tensor action on
`RegularAlgebra r ⊗[ℂ] E`. `universalSmoothRep` bundles that same action.
The coefficient carrier universe is independent of the field and point-group
universe; no finite-dimensionality is imposed on E.

The supplied semidirect decomposition and closedness of the actual unipotent
point subgroup define `inducingRepresentation`, `Induced`,
`inducedRepresentation`, `Jacquet`, and `jacquetRepresentation` by the generic
constructors, without replacing any carrier. The inducing action inflates
along h.projection and uses the positive half-modulus on the full parabolic.
Its smoothness uses continuity of that projection, the open kernel of the
positive half-character, and smoothness of the universal tensor.

The induced action is right translation on the full smooth function space.
`induced_covariant` states its actual full-parabolic covariance, and
`induced_action` states its translation formula. Smoothness follows from the
uniform open right stabilizer of each function. `Jacquet` is the actual
`Localization` character-one relation quotient of this induced model;
`jacquet_action_mk` states the inverse Levi half-modulus class-action formula,
and its smoothness follows from smoothness of the induced model and quotient
descent. No comparison of the full half-modulus with an inflated Levi character
is used.

These constructions apply to the point data in
`ConditionalParabolicIntertwiningStatement`, without splitness,
characteristic, or finite-dimensionality restrictions. Its connected-reductive
hypothesis supplies the required affine ambient group, while the same literal
point subgroups, decomposition, closedness, and continuous projection are the
inputs here. The construction asserts no noetherianity, projectivity,
admissibility, finite type, fiber isomorphism, geometric lemma, rationality,
or analytic continuation.
