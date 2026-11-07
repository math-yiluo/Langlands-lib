# Geometric inputs for canonical standard compression

This internal supporting unit constructs the geometric data used by compression
on the actual canonical standard representatives. It also specializes the named
native Jacquet inputs to every canonical standard Levi. It proves neither the
retained global statements nor the unrestricted uniform stabilization theorem.

## Exact maps and structural data

`standardCompressionRootPresentation` chooses a split component of
`Standard.leviScheme` using the proved split-component existence theorem, after
`standard_representatives_geometric` has supplied its reductivity. The existing
`parabolicRootPresentationOfDynamicStructure` then produces a root presentation
on exactly `Standard.parabolicHom` and `Standard.leviToParabolic`. The construction
uses the proved root-negation and dynamic-centralizer reductivity results; the
latter supplies the geometric-radical statement through its published reduction.
Generic minimality, parabolic recognition and standard-cocharacter existence
remain named inputs. The presentation's auxiliary torus need not be the ambient
chosen torus: its actual parabolic and Levi maps are the prescribed canonical
maps, which is what the compression comparison requires.

`standardCompression_semidirect` transfers a supplied literal-standard
semidirect decomposition to the represented groups using the three published
point-subgroup identities. `standardCompression_radical_isClosed` uses the same
radical identity and the proved closedness of standard unipotent subgroups.
`continuous_standardCompression_projection` rewrites the three groups, identifies
the supplied decomposition with the canonical standard decomposition by proof
irrelevance, and uses the proved continuity of that exact projection.
`compactSpace_standardCompression_leftQuotient` rewrites the parabolic point
subgroup and applies the existing standard quotient-compactness adapter. The
unproved dynamic quotient-compactness statement remains an explicit premise.

## Native inputs on the intrinsic Levi

`standardCompression_nativeJacquetInputs_of_statements` applies the general
`rationalCuspidalNativeJacquetInputs_of_statements` constructor to the canonical
standard Levi with its intrinsic torus factor. It discharges local reductivity
and geometric-radical recognition using `standard_representatives_geometric`,
intrinsic maximality using the standard-Levi torus-factor theorem, and intrinsic
genericity using `standardLeviStandardFamilies` with the proved `dynamicLie`.
The ambient `HasRelativeRootSystem` is inherited by the actual standard Levi
through `HasRelativeRootSystem.of_standardLeviTorusFactor`; no independent
root-system premise for each Levi is introduced. The preceding projection and
quotient lemmas supply the remaining geometric inputs.

The theorem works with any supplied root presentation on the canonical maps and
any supplied semidirect and closedness witnesses for the same exact groups. Its
conclusion is the unchanged `RationalCuspidalNativeJacquetInputs` predicate. The
remaining global premises are parabolic recognition, smooth maximal-split-torus
conjugacy, standard cocharacters, dynamic quotient compactness,
`RationalPointsIrreducibleAdmissibleStatement`, and
`RationalSupercuspidalJacquetFamilyFiniteStatement`. The first construction also
requires generic minimality. The chosen maximal split torus, generic
cocharacter, ambient actual root system and canonical rational-point topology
remain explicit. Locally compact and nonarchimedean group instances for the
ambient and Levi point groups are supplied to the final theorem, as they are to
the existing compression consumer.

The field universe `u` and carrier parameter `uV` are independent; both global
representation statements are used at `{u, max u uV}`, matching the existing
native bundle. This unit introduces no exponent and does not assert stability,
stationary power-chain equalities or complementarity for arbitrary smooth
representations.

## Provenance

These are internal compositions of the named Library constructions and proofs.
They fill the exact canonical-standard geometry and intrinsic-root inheritance
step between the existing native-input constructor and its standard-compression
consumer. They assert no additional theorem from the literature and retain each
unproved global structural or representation-theoretic input visibly.
