# Smoothness of the actual rational unitary scheme

Authors: Worker 57 (supplied splitting-and-descent proof), Worker 522
(published compatible-scalar normalization, adapted here), and Worker 539
(exact-target adaptation, verification and submission documentation).

`rationalUnitaryGroupSchemeSmooth` proves the published proposition
`RationalUnitaryGroupSchemeSmooth D`: for every selected family of complex
embeddings above the real embeddings, supplied Harris signature charts imply
smoothness of the structure morphism of `D.rationalUnitaryGroupScheme`.
It retains exactly the published number-field, quadratic-extension,
central-simple-algebra, involution and rational scalar-tower parameters.
There is no additional E/K/A scalar-tower hypothesis.

The private intermediate theorem `rationalUnitaryGroupSchemeSmooth_of_tower`
first works with compatible E/K/A scalars. It applies
`GroupScheme.GeneralLinear.smoothStatement` to each actual general linear
group over the complex base. The real embeddings of the number field form a
finite index type, so `GroupScheme.smooth_pi` gives smoothness of
`D.complexSplitUnitaryGroupScheme`. Forgetting group laws in
`D.directComplexUnitaryGroupSchemeIso C` gives an isomorphism over Spec(C),
and `GroupScheme.smooth_of_over_iso` transfers smoothness to the actual
rational unitary scheme pulled back directly to Spec(C).

Then `rationalComplexBaseMap_fpqc` supplies surjectivity, flatness and
quasi-compactness of the actual map Spec(C) to Spec(Q).
`MorphismProperty.of_pullback_snd_of_descendsAlong`, using Mathlib's fpqc
descent instance for smooth morphisms, descends the established pullback
smoothness to `D.rationalUnitaryGroupScheme.X.hom`.

The closing theorem constructs the needed compatible E-action on K internally,
following the normalization in the published `rationalGroupSchemeSmooth`
proof. Centrality puts each E-scalar of A in the image of K. Simplicity makes A
nontrivial, so the field map from K to A is injective. Chosen preimages therefore
form a ring map from E to K whose composite with K to A is the original E-action
on A. With this algebra structure, the rational dimension formula preserves the
quadratic extension degree. The underlying absolute CM conjugation on K is
unchanged, so the original involution, its action on the center and the
central-simple datum apply. The original chart equivalences and their
compatibilities also apply, since the actions on A are unchanged. The actual
rational scheme uses the preserved rational basis and rational involution;
its multiplier kernel is therefore unchanged. Applying the private theorem to
these data proves the original target with its full published parameter list.

The provenance is internal: this proof combines the published general linear
smoothness, finite-product closure, actual complex splitting, faithfully flat
scalar comparison and compatible-scalar normalization. The unitary group
remains the genuine scheme-theoretic multiplier kernel throughout.
Smoothness of kernels is not an input. The theorem is conditional on supplied
charts; it establishes no chart-existence, reductivity or Shimura moduli
representability result.
