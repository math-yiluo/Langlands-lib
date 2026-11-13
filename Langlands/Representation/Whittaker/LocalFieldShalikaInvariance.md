# Shalika invariance of Whittaker bi-equivariant distributions over every local field

Author: Worker 5089.

The published `Langlands.Whittaker.shalikaDistributionInvariance` proves
`ShalikaDistributionInvarianceStatement`, which quantifies over `PadicField` only. Its
proof is a chain of Bruhat-cell theorems (`BruhatHaarMeasureProof`,
`BruhatOrbitalIntegrationProof`, `BruhatFiberCharacterCovarianceProof`,
`BruhatCompatibleSupportProof`, `BruhatCellFactorizationProof`,
`BruhatCellVanishingProof`, `BruhatCellInvarianceProof`, `DistributionInvarianceProof`).
Each of these statements is also p-adic only. Their proofs, however, use the p-adic
structure only to install topological instances: the canonical normed field, local
compactness, second countability and the nonarchimedean property of `GL_(n+1)` and of
its upper unipotent subgroup, and a compact open subgroup. All the remaining lemmas
they apply are stated for general fields.

This module repeats each step of that chain for an arbitrary nonarchimedean local field

```lean
variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
```

of any characteristic. The topological facts come from
`Langlands.Group.GL.LocalFieldTopology`, installed with `attribute [local instance]`:
Hausdorffness and total disconnectedness of `F`, local compactness and total
disconnectedness of `Fˣ`, local compactness, second countability and total
disconnectedness of `GeneralLinear (n + 1) F`, and local compactness and the
nonarchimedean property of `upperUnipotent (n + 1) F`. The compact open subgroup is
`LocalFieldTopology.generalLinear_compactOpen`. Each proof is otherwise the published
p-adic proof with `F.Carrier` replaced by `F`, and it applies the same general lemmas.

## Declarations

All are in the namespace `Langlands.Whittaker.LocalField`. Each theorem states the
content of the p-adic statement named in its docstring, with `F` and `n` explicit
instead of a quantified prime and `PadicField`.

- `bruhatHaarMeasure F n`: Haar measures exist on `U = upperUnipotent (n + 1) F` and on
  every `permutationUnipotentPlus (n + 1) F w`. They are right invariant and
  sigma-finite, and on `U` they are preserved by `weylTransposeUnipotent n F`. The
  content of `BruhatHaarMeasureStatement`. The proof applies
  `RankinSelberg.unipotent_exists_compact_open F n` (already stated over a general local
  field) together with the published helpers `isMulRightInvariant_of_compactOpenCover`,
  `map_eq_self_of_antiInvolution` and `compactOpenCover_of_le`.
- `bruhatOrbitalIntegration F n w`: for each right-invariant Haar measure on the fiber
  group, there is a unique surjective, support-controlled linear orbital integration from
  test functions on `U × ((Fin (n + 1) → Fˣ) × U)` to test functions on the upper Bruhat
  cell, given pointwise by `bruhatFiberAverage`. The content of
  `BruhatOrbitalIntegrationStatement`. It applies `existsUnique_bruhatOrbitalIntegration`
  with the coordinates `upperBruhatCoordinates`, the factorization
  `upperUnipotentFactorization`, and the compact open neighborhood of `1` in the fiber
  group cut out by a compact open subgroup of `GL_(n+1)(F)`.
- `bruhatFiberCharacterCovariance F n ψ w`: the character average of a test function
  pulled back by Shalika's fiber action at `u` equals the original average times the
  inverse of `compatibilityDefect ψ n w u d`. The content of
  `BruhatFiberCharacterCovarianceStatement`. The computation is the p-adic one: a change of
  variables by right and left translation on `U × U`, with `compatibilityDefect_eq_div`.
- `bruhatCompatibleSupport F n ψ w`: a distribution `τ` on the torus whose character
  average dual is invariant under the fiber action is supported on
  `compatibleTorus ψ n w`. The content of `BruhatCompatibleSupportStatement`. This uses
  surjectivity of the character average (`SchwartzBruhat.characterAverageSurjective`), the
  covariance above, and local constancy of each defect function
  (`RankinSelberg.isLocallyConstant_of_continuous_complex_character`). Then
  `BruhatCompatibleSupport.apply_eq_zero_of_local` turns the local vanishing into global
  vanishing.
- `bruhatCellFactorization F n ψ w`: a bi-equivariant distribution `D` on the cell,
  composed with the orbital integration, factors uniquely through the character
  average by a distribution `τ` supported on the compatible torus. The content of
  `BruhatCellFactorizationStatement`. It uses
  `Distribution.characterAverageFactorization` and the published orbital-integral
  translation lemmas of `BruhatCellFactorization`.
- `bruhatCellVanishing F n ψ w hempty D hD`: if the compatible torus is empty, every
  bi-equivariant cell distribution vanishes. The content of
  `BruhatCellVanishingStatement`.
- `bruhatCellInvariance F n ψ w hnon`: if the compatible torus is nonempty, the
  Weyl-conjugated transpose preserves the cell. Every bi-equivariant cell distribution is
  then invariant under it. The content of `BruhatCellInvarianceStatement`. The proof
  uses the published lemmas of `BruhatCellInvariance`: `characterAverage_productTranspose`,
  `supportedOn_middle_of_factorization`, `bruhatFiberAverage_productTranspose`,
  `upperBruhatTorusMap_productTranspose` and `cell_stable_of_fixed_monomial`.
- `shalikaDistributionInvariance F n ψ D hD`: every algebraic distribution `D` on
  `GeneralLinear (n + 1) F` that is bi-equivariant for the standard character of `ψ` on
  the upper unipotent subgroup (`IsBiEquivariantDistribution ψ n D`) is invariant under
  the Weyl-conjugated transpose `g ↦ J gᵗ J` (`IsWeylTransposeInvariant n F D`). This is
  the content of `ShalikaDistributionInvarianceStatement` for every nonarchimedean local
  field.

## Proof of `shalikaDistributionInvariance`

The difference `E = D - pushforward (weylTransposeHomeomorph n F) D` is again
bi-equivariant. Two private lemmas show this: `pullback_transpose_biTranslate`
rewrites a transposed bi-translate, and `biEquivariant_difference` uses
`standardCharacter_weylTranspose`. `E` is anti-invariant by
`pushforward_weylTranspose_involutive`. The published all-field
`bruhatFiltrationVanishing` reduces `E = 0` to vanishing on each Bruhat-cell
neighborhood. The published all-field `bruhatCellRestrictionVanishing` reduces that to
one of two cell alternatives. If the compatible torus of `w` is empty,
`bruhatCellVanishing` gives the first. Otherwise `bruhatCellInvariance` gives the
second. Hence `E = 0`, that is, `D` is Weyl-transpose invariant.

## Provenance

The source is J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193 (registered `shalika-1974-multiplicity-one`), Theorem 1.6 and
its proof (printed pp.174–179), in Shalika's §1, "Local theory: The 𝔓-adic case".
The companion Markdown of the p-adic modules named above records how their
implementation follows and adapts that argument. This module is an internal
generalization of those proofs to every nonarchimedean local field. It
introduces no new transcription from the literature and keeps the published p-adic
argument unchanged apart from the source of the topological instances. It supports
`Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof`.
