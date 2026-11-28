# Continuous rational extensions of functions on the norm-one group

Let `G` be a connected reductive group over a number field `F`. The module
`Langlands.Global.AdelicNormOneExtension` extends functions on `G(𝔸_F)¹` to `G(𝔸_F)` along a chosen
retraction, so that the constant terms and truncation of the Library, which are defined for
functions on `G(𝔸_F)`, apply to them. All declarations are in `Langlands.Global`.

- `normOneRetraction hG`, a chosen continuous map `G(𝔸_F) → G(𝔸_F)¹` given by
  `exists_normOneRetraction`. It fixes `G(𝔸_F)¹` (`normOneRetraction_coe`) and satisfies
  `r(g x) = g r(x)` and `r(x g) = r(x) g` for `g ∈ G(𝔸_F)¹` (`normOneRetraction_mul_left`,
  `normOneRetraction_mul_right`).
- `normOneExtension hG ψ = ψ ∘ normOneRetraction hG`. It agrees with `ψ` on `G(𝔸_F)¹`
  (`normOneExtension_coe`) and is continuous when `ψ` is (`continuous_normOneExtension`).
- `normOneExtension_rational_mul`: if `ψ` is left invariant under the rational norm-one points, the
  extension is left invariant under `G(F)`, because `G(F) ⊆ G(𝔸_F)¹` and `r` is left equivariant.
- `normOneExtensionCRF hG ψ hψ hinv`, the extension as an element of `ContinuousRationalFunctions F G`
  (through `continuousQuotientLinearEquiv` and the quotient `G(F) \ G(𝔸_F)`), with
  `evaluate_normOneExtensionCRF` recovering `normOneExtension hG ψ`.
- `normOneExtension_mul_ofFinite`: right invariance of `ψ` under a compact finite level `K₀` passes to
  the extension, by right equivariance of `r`.
- `measurable_normOneExtension_family`: joint measurability of families passes to the extensions.
