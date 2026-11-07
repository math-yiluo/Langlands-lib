# Dynamic-output native fixed modules from finite orbit geometry

This internal adapter connects the published actual universal native support-admissibility theorem to the literal dynamic output used by `RationalSupercuspidalJacquetFamilyFiniteStatement`. It proves the conditional fixed-module result `RationalNormalized.outputJacquet_fixedModule_finite_of_geometry`; it does not prove the global statement. Finite ordered double-coset geometry, actual dynamically realized intersection data and compactness of the original target-intersection parabolic quotients remain explicit inputs.

The coefficient algebra is the unchanged `RationalNormalized.RegularAlgebra r`, formed using the complete `parabolicLeviRationalNormCharacters r` family. The universal tensor, full induced-function carrier, character-one native coinvariant quotient and inverse output half character are unchanged. The field and group schemes use universe `u`; the inducing complex representation has the independent carrier universe `uV`.

## Explicit finite geometry

`RationalNormalized.NativeJacquetFiniteOrbitGeometry` is a type of actual geometric data for the fixed source root presentation, supplied radical and represented output triple. Its fields are a finite length, an `OrderedDoubleCosets` ordering, actual intersection data at the inverse representatives, their `DynamicRealization` witnesses, and compactness of each original target-intersection parabolic quotient in the original output Levi topology. It contains no coefficient representation, admissibility assertion or representation-filtration conclusion. The source multiplication proof in its intersection fields is the one derived from the supplied source radical below. The subsequent theorems expose these same inputs separately.

## Supplied radical and source multiplication

`ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical` proves the Levi-first scheme multiplication isomorphism for any supplied geometric radical `n` of the original source parabolic. The compatible root presentation supplies a split-component cocharacter whose dynamic parabolic and centralizer are the original source parabolic and Levi. The published `range_comp_radical_eq` identifies the ambient image of `n` with the unipotent group of that cocharacter. Closed subgroup monomorphisms provide the represented-subfunctor witnesses, and `Dynamic.isIso_subgroupMultiplication` gives the isomorphism with the original maps `l` and `n`. Smoothness of the ambient scheme is explicit. The theorem removes a separate source multiplication premise without changing the supplied radical.

## Equal subgroup presentations

`UnramifiedNormalized.isAdmissible_jacquetRepresentation_of_subgroup_eq` transports admissibility when the radical subgroups and Levi subgroups are equal inside the same topological group. Substitution reduces the source and target to the same `jacquetRepresentation`; proof irrelevance accounts for their closedness and normalizer witnesses. Thus this is equality transport of the same quotient and its exact normalization character, not an identification with an auxiliary representation.

## Original target quotient and the dynamic output

`RationalNormalized.outputJacquet_isAdmissible_of_geometry` assumes the actual source root presentation, supplied geometric radical, original point semidirect decomposition, closedness of its radical points, continuous source projection, and compactness of the original source parabolic quotient. The ambient group scheme is smooth, affine and connected reductive over a nonarchimedean local field, and the original rational-point group is locally compact and nonarchimedean. The source complex representation is admissible and satisfies the published actual `IsSupercuspidal r` vanishing predicate.

The output is presented by actual parabolic, Levi and geometric radical maps `q`, `lQ`, `nQ`, with their multiplication isomorphism. The two subgroup-functor equalities `hL` and `hN` say that their ambient images are the centralizer and unipotent subfunctors of the specified output cocharacter. The other inputs are:

- A finite `OrderedDoubleCosets (pointImage p) (pointImage q) m`, including the covering and open initial-union conditions needed for the support filtration.
- An actual `GeometricLemmaIntersectionDatum` for each inverse ordered representative, using the original source and target maps and the source multiplication isomorphism proved above.
- A simultaneous `DynamicRealization` of each datum.
- Compactness of `LeftQuotient (pointImage (D i).q')` in the rational points of the original output Levi, equipped with `leviPointTopology lQ hlQ`.

The proof obtains Hausdorffness of rational points from the affine scheme and the local-field topology. It obtains second countability from the connected-reductive rational-point theorem, and then sigma compactness from local compactness and second countability. For each orbit, `compactComparisonSaturation_comap_section` rewrites the quotient required by the native orbit theorem to the literal target-intersection subgroup inside the output Levi image. The published `targetIntersectionQuotient_compactSpace` transfers the supplied original parabolic-quotient compactness through its actual point-group homeomorphism. No compactness premise is imposed on an unrelated comparison quotient.

The published `universalNativeJacquet_isAdmissible` now applies: it constructs support images in the actual native quotient, identifies their grades with the original normalized orbit quotients, derives each grade's admissibility from source supercuspidality and the geometric inputs, and assembles them over the already proved Noetherian complete regular algebra. Here it produces admissibility with output subgroups `pointImage (nQ ≫ q)` and `pointImage (lQ ≫ q)`.

Evaluating `hN` and `hL` at the rational-point test scheme identifies those exact point images with the literal dynamic unipotent subgroup and `outputLeviPoints` of the cocharacter. The equality-transport lemma then gives admissibility of `outputJacquetRepresentation r h hU sigma chi` itself, including its specified inverse half normalization.

## Fixed-module finiteness and retained obligations

`RationalNormalized.outputJacquet_fixedModule_finite_of_geometry` takes the finite-generation component of that admissibility theorem at any `OpenSubgroup (outputLeviPoints chi)`. Its conclusion is exactly

```lean
Module.Finite (RegularAlgebra r)
  (fixedVectors (outputJacquetRepresentation r h hU sigma chi) J.toSubgroup)
```

This also applies to every compact open subgroup in the global target. The definition of coefficient admissibility used here quantifies over all open subgroups, so this final extraction does not need an additional compactness premise on `J`.

The provenance is internal composition of `NativeJacquetSupportAdmissibility`, the original target quotient comparison in `RepresentedGeometricLemmaTargetInduction`, the radical identification in `ParabolicRootRadicals`, and the rational-point second-countability theorem. It completes their exact-output adapter. Existence of finite ordered representatives with the required actual intersection data and simultaneous dynamic realizations, and compactness of their original target-intersection quotients, are still unproved here. These remain obligations for the unchanged global statement; this conditional contribution neither assumes coefficient admissibility nor supplies global geometric existence.
