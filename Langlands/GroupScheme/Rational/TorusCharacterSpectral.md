# Spectral valuations of anisotropic torus character values

This internal adapter proves `AnisotropicTorusSpectralUnitsStatement` at
arbitrary universe `u`. For an actual nonarchimedean local field `F`, a finite
Galois extension `E`, and an affine anisotropic torus locally of finite type,
every `E`-rational character evaluated on the extension of an `F`-rational
point has spectral valuation one. The valuation is
`Langlands.LocalGalois.spectralValuation F E`, constructed using the canonical
`localNormedField F`. The character and point comparisons are the actual
`rationalCharacterEval` and `GaloisPointComparison.rationalExtend` maps.
Anisotropy is the imported split-rank-zero condition.

The supporting theorem
`IsAnisotropic.spectralValuation_characterEval_eq_one_of_closedTorus` proves
the same conclusion when the torus is a closed subgroup of any anisotropic
group scheme. Affineness and local finite type of the torus are explicit.
No reductivity hypothesis on the ambient group is needed for this helper.
The final theorem `anisotropicTorusSpectralUnits_proof` specializes it to the
identity closed subgroup of the torus.

The implemented norm argument starts with a complete nontrivially normed
ultrametric field `F` and a finite Galois extension `E`, in independent
universes `u` and `v`. The field norm is the product of the conjugates over
all `F`-algebra automorphisms of `E`. Each automorphism preserves the spectral
norm. Multiplicativity and extension of the base norm therefore give
`spectralNorm F E x ^ Fintype.card (E ≃ₐ[F] E) = ‖Algebra.norm F x‖`.
The automorphism type contains the identity, so its cardinality is nonzero.
Nonnegativity of the spectral norm then shows that field norm one implies
spectral norm one.

For a closed torus inside an anisotropic group, the imported theorem
`IsAnisotropic.algebraNorm_characterEval_eq_one_of_closedTorus` supplies
field norm one for the character value. Applying the preceding argument
gives spectral norm one, which is precisely the asserted equality of
nonnegative-real spectral valuations. This does not assert that the
character value itself equals one.

The separate theorem `localField_spectralValuation_valuativeExtension`
works for every algebraic extension `E : Type v` of `F : Type u`, without a
finiteness or Galois hypothesis. It equips `E` with the valuative relation
induced by the spectral valuation and proves `ValuativeExtension F E` for
the original given relation on `F`. The proof rewrites the spectral norm
of base-field scalars using `spectralNorm_extends`, then applies
`localNormedField_le` and compatibility of the canonical valuation with the
original relation. Thus this comparison preserves and reflects that
relation, rather than merely comparing two newly chosen base valuations.

The provenance is an internal composition of the published anisotropic
torus norm-character theorem, the canonical local-field norm comparisons,
and Mathlib's `Algebra.norm_eq_prod_automorphisms`,
`spectralNorm_eq_of_equiv`, multiplicative spectral norm, and
`spectralNorm_extends`. The argument is documented here directly from its
implementation; it makes no additional original-literature assertion.

There is no characteristic-zero or positive-rank restriction. The torus
statement requires a finite Galois extension, while the separate valuation
extension comparison permits arbitrary algebraic extensions and independent
universes. These results do not construct semisimple replacements of group
points, place such points in maximal tori, identify eigenvalues of arbitrary
representations with character values, or prove the general reductive
spectral integrality or compactness targets.
