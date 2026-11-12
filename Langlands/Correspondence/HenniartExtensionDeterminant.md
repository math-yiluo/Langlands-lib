# Determinants, central characters and the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionDeterminant`.

Henniart (2000), §4.3 ("`ω_{π(σ)} ∘ rec = det σ` ... découle aussi de 3.8"),
extended by unramified twists as in §4.4.

## Lemmas

`FiniteRepresentation.determinantCharacterClass_twistClass` (namespace
`Langlands.FiniteRepresentation`): the determinant character of the twist of a
class of rank `n` by `χ` is `χ ^ n` times its determinant character. On
representatives this is `LinearMap.det_smul`.

In namespace `Langlands.Henniart.Extension`:

- `supercuspidalCentralActsBy_iff`: for an actual supercuspidal representative
  `A`, the published `SupercuspidalCentralActsBy` on its class is the scalar
  action on `A`. The forward direction is the published
  `AssemblyDeterminant.centralActsBy_apply`; the reverse uses
  `A.toIrreducibleAdmissible` as witness.
- `supercuspidalCentralActsBy_twist`: twisting by `χ ∘ det` multiplies the
  central action of `a` by `χ(a) ^ n`. The twisted representation acts by
  `χ(det(a · 1)) • A(a · 1)` on the same carrier, and
  `det(a · 1) = a ^ n` (`Matrix.GeneralLinearGroup.det_scalar`).

## Compatibility

`extensionMap_determinant`: the published `SupercuspidalDeterminantCompatibility`
for a geometric candidate `e`. Let `σ = z b₀` be a stable decomposition with
image `π₀` of rank `n`. The candidate supplied by the stable image satisfies the
determinant clause of 3.8: some `ω` is the central character of `π₀`
(published `isUnitaryCentralCharacter_generator_iff`) with
`ω(rec w) = det b₀ (w)` (published `unitaryDeterminant_generator`). By the two
lemmas, for every `w`:

- the extension `(fieldUnramified z)`-twist of `π₀` acts at `rec w` by
  `(z ^ ord(rec w)) ^ n · ω(rec w)`;
- `det σ (w) = (z ^ deg w) ^ n · det b₀ (w)`, since `weilClassForget σ` is the
  twist of the underlying class of `b₀` by the unramified character
  (`underlyingClass_twistBasisEquiv`) and its rank is `n`.

These agree because `ord(rec w) = deg w` for a geometric candidate (published
`ord_reciprocityHom`).
