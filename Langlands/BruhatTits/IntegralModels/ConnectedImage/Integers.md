# The integers of a finite Galois extension of the maximal unramified extension

Author: Worker 33.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` (the
maximal unramified extension of `F` inside `F^sep = SeparableClosure F`) and
`O = fixedFieldIntegers F`, its valuation ring. For an intermediate field `L`
of `F^sep / K`, the Library valuation `intermediateValuation F L` restricts to
`L` the spectral valuation of `F^sep`. This module shows that its valuation
ring `O_L` is the integral closure of `O` in `L`. When `L / K` is finite and
Galois, it also shows that `O_L` is a finite free `O`-module with
`K ⊗[O] O_L ≃ L`. All declarations are in the namespace
`Langlands.BruhatTits.IntegralModels.ConnectedImage`.

## Provenance

This is internal supporting material for the proof of
`UnramifiedTorusIwahoriConnectedImageStatement`. Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, Section B.3
and Lemma B.3.1 (printed pp. 656–657 / PDF pp. 687–688), use the ring of
integers `o_ℓ` of a finite separable extension and the model
`R_{o_ℓ/o} 𝔾ₘ`. That construction uses, without separate statement, that
`o_ℓ` is finite and free over `o`, and that `ℓ = k ⊗_o o_ℓ` (used in the proof of Lemma A.3.12, printed p. 598 /
PDF p. 629). The source treats these as standard facts. Here they are proved
for the valuation ring of `intermediateValuation F L` over the Library's `O`.
The proofs use Mathlib's integral-closure theory over a discrete valuation ring
and are not taken from the source.

## Declarations

- `integers F L : ValuationSubring L` is the valuation ring of
  `intermediateValuation F L` (an abbreviation). `mem_integers_iff`: `x ∈ O_L`
  exactly when its valuation is `≤ 1`.
- `isUnit_integers_iff`: an element of `O_L` is a unit of `O_L` exactly when
  its valuation is `1`. If `x y = 1` with both valuations `≤ 1` and one of
  them `< 1`, the product would have valuation `< 1`. Conversely, valuation
  `1` puts `x⁻¹` in `O_L`.
- Local instances (visible only in this file) give the algebra structures of
  `O` on `L` and on `F^sep` explicitly through `K`, with the scalar towers
  `O → K → L`, `O → O_L → L` and `O → L → F^sep`. They are explicit because
  instance search through the valuation-subring and intermediate-field
  coercions is slow; they are definitionally the composites through `K`.
- `baseToFixedIntegers F` is the ring map from the integers of `F` (for the
  Library's normed-field structure `localNormedField F`) to `O`.
- `isIntegral_integers`: every element of `O_L` is integral over `O`. Its
  image in `F^sep` lies in the extension integers of `F^sep` for the spectral
  valuation. The Library theorem `spectral_integral` (module
  `Langlands.Galois.Local.SpectralProof`) makes it integral over the integers
  of `F`, hence over `O`. Integrality descends from `F^sep` to `L` because
  `L → F^sep` is injective.
- `isIntegralClosure`: the instance `IsIntegralClosure O_L O L`. An element of
  `L` integral over `O` is integral over `O_L`. Since a valuation ring is
  integrally closed, it lies in `O_L`. The converse is the previous lemma.

For the remaining declarations `L / K` is finite and Galois. The local
instance `integersDVR` takes `O` to be a discrete valuation ring from the
Library theorem `separableUnramifiedArithmetic`.

- `integers_finite`, `integers_free`, `integers_projective`: `O_L` is a finite,
  free and projective `O`-module. Finiteness is Mathlib's
  `IsIntegralClosure.finite` (for a Dedekind domain `O` with fraction field `K`
  and the finite separable extension `L / K`). Freeness is
  `IsIntegralClosure.module_free` for the principal ideal domain `O`, using
  that `L` is torsion-free over `O`.
- `integers_isPushout`: `Algebra.IsPushout O K O_L L`. Mathlib's
  `IsIntegralClosure.isLocalization` shows that `L` is the localization of
  `O_L` at the nonzero elements of `O`, and
  `Algebra.isPushout_of_isLocalization` turns this into a pushout square.
- `tensorEquiv F L : K ⊗[O] O_L ≃ₐ[K] L` is the resulting isomorphism, with
  `tensorEquiv_tmul : a ⊗ b ↦ a • b`.
- `piTensorEquiv F L I : K ⊗[O] (I → O_L) ≃ₐ[K] (I → L)`, for a finite index
  type `I`, is Mathlib's `Algebra.TensorProduct.piRight` followed by
  `tensorEquiv` in every coordinate. `piTensorEquiv_tmul` gives its value on a
  pure tensor coordinatewise.
