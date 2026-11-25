# Whittaker decay classes are stable under transpose inverse

Module `Langlands.Global.RankinSelberg.DualWhittakerCore.DualDecay`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. This helper module is internal to the proof of
`DualCuspidalWhittakerExpansionStatement` (module `DualWhittakerExpansionProof`). Provenance:
internal. It shows that the hypotheses of the majorant theorem `whittakerMajorantsStatement_proof`
(module `WhittakerExpansionCore.WhittakerStep`) pass from a space of functions `f`
to the space of the functions `f ∘ ι`, where `ι(g) = ᵗg⁻¹` is the Library `iota`.

Notation. `Points F n` are the adelic points of `GL_n` over the number field `F`.
`finitePoint F n l` is the point with finite component `l` and archimedean component `1`, and
`archPoint F n Z hZ` (for an archimedean matrix `Z` with `Z * Z = 0`) is the point with
archimedean component `1 + Z` and finite component `1`; both are defined in
`WhittakerExpansionCore.Interface`. `detNorm F n g = |det g|`. A `WhittakerDecayClass F r V R`
(module `Interface`) is a complex space `V` of functions on `Points F (r + 1)` with a real-linear
family `R Z` of linear maps `V → V` such that every `f ∈ V` is continuous, left invariant under
the rational points, right invariant under some open subgroup of `GL_(r+1)(𝔸_f)` through
`finitePoint`, bounded on every determinant band `lo ≤ |det x| ≤ hi` with `0 < lo`, and such that
for `Z * Z = 0` the derivative of `t ↦ f(x · archPoint(t Z))` at `t = 0` is `(R Z f)(x)`.

The file sets `backward.isDefEq.respectTransparency false` and declares the affineness and
smoothness instances of the group schemes as local instances, as the Library modules do.

## Points (section `Points`)

The four component and inclusion identities below retain their original names
and proofs and are imported from `Global/AdelicGLInverseTranspose`.

* `infinite_inverseTranspose`, `finite_inverseTranspose`: transpose inverse commutes with the
  archimedean and finite components of an adelic matrix.
* `inverseTranspose_ofFinite`, `inverseTranspose_ofInfinite`: and with the embeddings of the
  finite and archimedean groups.
* `neg_transpose_mul_self_eq_zero`: if `Z * Z = 0` then `(-ᵗZ) * (-ᵗZ) = 0`.
* `inverseTranspose_squareZeroElement`: `ᵗ(1 + Z)⁻¹ = 1 - ᵗZ` for `Z * Z = 0`, since
  `(1 + Z)⁻¹ = 1 - Z`.
* `iota_finitePoint`: `ι(finitePoint l) = finitePoint(ᵗl⁻¹)`.
* `iota_archPoint`: `ι(archPoint Z) = archPoint(-ᵗZ)`.
* `archPoint_congr`: `archPoint` depends only on the matrix, not on the proof of `Z * Z = 0`.
* `iota_mem_rationalSubgroup`: `ι` maps the rational subgroup into itself (Library
  `iota_rational`).

## The transported space (section `Space`)

* `iotaComp F n : (Points F n → ℂ) ≃ₗ[ℂ] (Points F n → ℂ)` is `f ↦ f ∘ ι`
  (`iotaComp_apply`, `rfl`).
* `iotaSpace F V` is the image of `V` under `iotaComp`, and `iotaSpaceEquiv F V : V ≃ₗ[ℂ]
  iotaSpace F V` is `f ↦ f ∘ ι` (`coe_iotaSpaceEquiv`, `rfl`).
* `coe_iotaSpace`: every `f ∈ iotaSpace V` is `g ∘ ι` for its preimage
  `g = (iotaSpaceEquiv F V).symm f ∈ V`.

## Derivatives and the decay class (section `Derivative`)

* `iotaDerivative F V R Z` is `f ↦ (R(-ᵗZ) g) ∘ ι` with `g` the preimage of `f`, that is,
  `iotaSpaceEquiv ∘ R(-ᵗZ) ∘ iotaSpaceEquiv⁻¹`. It is real-linear in `Z` because
  `Z ↦ -ᵗZ` is. `coe_iotaDerivative` (`rfl`) gives its values.
* `whittakerDecayClass_iotaSpace`: if `(V, R)` is a `WhittakerDecayClass`, then so is
  `(iotaSpace V, iotaDerivative R)`. For `f = g ∘ ι`:
  - continuity: `g` and `ι` are continuous (`continuous_iota`);
  - rational invariance: `f(y x) = g(ι(y) ι(x))` with `ι(y)` rational (`iota_mul`);
  - finite level: if `g` is invariant under the open subgroup `L`, then `f` is invariant under
    the open subgroup `{l : ᵗl⁻¹ ∈ L}` (`iota_finitePoint`; transpose inverse is continuous);
  - band bounds: `|det ι(x)| = |det x|⁻¹` (`detNorm_iota`), so the band
    `lo ≤ |det x| ≤ hi` maps into the band `(max hi lo)⁻¹ ≤ |det| ≤ lo⁻¹`, where `g` is bounded;
  - derivatives: `f(x · archPoint(t Z)) = g(ι(x) · archPoint(t (-ᵗZ)))` (`iota_mul`,
    `iota_archPoint`, `archPoint_congr`), so the derivative at `t = 0` is
    `(R(-ᵗZ) g)(ι x) = (iotaDerivative R Z f)(x)`; note that `-ᵗZ` is again square-zero.
