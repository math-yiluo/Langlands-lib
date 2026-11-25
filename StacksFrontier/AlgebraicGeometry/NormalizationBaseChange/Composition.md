# Normalized base change along a tower of bases

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Composition`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let X be a scheme over T₁ with normalization ν. For a map T ⟶ T₁, write V and W for the
base changes of the normalization and of X respectively. The file gives conditions under
which V and W have isomorphic normalizations over W.

## Comparison of the normalizations

- `NormalizedBaseChange.baseChangeMap` constructs V ⟶ W from any two pullback squares.
  `isPullback_baseChangeMap` identifies it as a base change of ν, so it inherits integrality
  and remains an isomorphism over the pullback of any open on which ν is an isomorphism.
- `isBirational_baseChangeMap` proves birationality when V and W are topologically
  Noetherian, both projections to the original schemes are open, and ν is an isomorphism
  over a dense open with dense inverse image.
- `exists_normalizationScheme_iso_baseChangeMap_normalization` gives an isomorphism from
  the normalization of W to that of V, commuting with the maps to V and W. It requires
  finitely many irreducible components on each quasi-compact open of X and W and on the
  preimage in V of each such open in W, together with birationality over those opens of W.
- `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isBirational` uses global
  birationality when V and W are locally Noetherian. The version
  `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isOpenMap` obtains
  birationality via `isBirational_baseChangeMap_normalization` from openness of the
  projections from V and W to the original schemes. It requires X reduced, ν locally
  of finite type, and X, its normalization, V and W topologically Noetherian, with V
  and W also locally Noetherian.
- `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing` derives
  the Noetherian conditions for reduced X quasi-compact and locally of finite type over a
  Noetherian ring A, with finite ν and base change to a Noetherian A-algebra. It uses
  `noetherianSpace_of_locallyOfFiniteType` for the underlying topology and still takes
  the component finiteness witness for X and openness of both projections.

The comparison uses the normalization factorization for integral maps that are birational on
quasi-compact opens. In the open-map case the projections preserve density under inverse image,
so the isomorphism on a dense open gives a bijection on generic points and isomorphisms on
their stalks.

References include Tag 035Q and Tag 09IK.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/Composition.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
