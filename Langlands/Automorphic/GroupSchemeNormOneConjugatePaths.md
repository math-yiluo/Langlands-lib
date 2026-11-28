# Conjugated coordinate paths in the archimedean norm-one group

Let `A : NormOneLieAtlas F G hsmooth e` be an embedded Lie atlas on `G(F∞)¹` and let
`Ψ : E → G(F∞)` be a smooth map from a finite-dimensional real normed space with values in
`G(F∞)¹` and `Ψ(0) = 1`. The module `Langlands.Automorphic.GroupSchemeNormOneConjugatePaths`
constructs the paths `s ↦ k⁻¹ Ψ(s v) k` in `G(F∞)¹`, proves that they are smooth for `A`, and
bounds their velocities. They are the paths along which a function is compared with its
translate by an archimedean point `k⁻¹ Ψ(v) k` in the oscillation estimate of
`Langlands.Global.AdelicNormOneFamilyDecay`. All declarations are in
`Langlands.Automorphic.GroupSchemeFunctions`.

- `conj_mem_infiniteNormOneSubgroup`: conjugation by `G(F∞)` preserves `G(F∞)¹`.
- `contMDiff_infiniteNormOne_of_val`: a continuous map into `G(F∞)¹` whose composite with the
  inclusion into `G(F∞)` is smooth is smooth for the atlas `A`. This is
  `ContMDiff.iff_comp_isImmersion` applied to the immersion `A.immersion`.
- `conjugateDisplacement Ψ hΨ₁ k z y = k⁻¹ Ψ(z)⁻¹ Ψ(y) k ∈ G(F∞)¹`, jointly smooth in `(k, z, y)`
  (`contMDiff_conjugateDisplacement`).
- `conjugateDifferential A Ψ hΨ₁ (k, z)`, the differential at `y = z` of
  `y ↦ k⁻¹ Ψ(z)⁻¹ Ψ(y) k`, a linear map `E → (Fin e → ℝ)` into the tangent space at the identity.
  It depends continuously on `(k, z)` (`continuous_conjugateDifferential`).
- `conjugatePath Ψ hΨ₁ k v : s ↦ k⁻¹ Ψ(0)⁻¹ Ψ(s v) k`, a smooth path for `A`
  (`contMDiff_conjugatePath`) starting at the identity (`conjugatePath_zero`); when `Ψ(0) = 1` its
  value is `k⁻¹ Ψ(s v) k` (`conjugatePath_val`).
- `leftPathVelocity_conjugatePath`: the velocity at `s`, translated to the identity, is
  `conjugateDifferential A Ψ hΨ₁ (k, s v) v`.
- `exists_norm_conjugateDifferential_le`: for a compact set of `k` and `v` in a closed ball, this
  velocity has norm at most `C ‖v‖` for `s ∈ [0, 1]`, by continuity of the differential on the
  compact set of pairs `(k, s v)`.
