# Relative normalizations over an affine scheme

- `finite_geometricallyReduced_normalization`: let `Z` be affine over `Spec R'`, and `φ : W → Z.left`
  quasi-compact and quasi-separated. Suppose the integral closure of `Γ(Z, ⊤)` in `Γ(W, φ⁻¹ ⊤)` is a
  finite `Γ(Z, ⊤)`-module and reduced after `F ⊗[R'] -` for every field `F`. Then the normalization
  map `φ.fromNormalization` is finite, and `φ.fromNormalization ≫ Z.hom` is geometrically reduced.
  Finiteness uses `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` and Mathlib's description of
  the sections of the normalization over an affine open (`normalizationObjIso`,
  `fromNormalization_app`). Geometric reducedness uses `geometricallyReduced_of_isAffine`.
