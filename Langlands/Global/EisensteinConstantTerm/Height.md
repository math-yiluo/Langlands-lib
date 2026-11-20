# Heights, twists and character lattices for the constant-term formula

Module `Langlands.Global.EisensteinConstantTerm.Height`. Facts about the Library's Iwasawa
height `IsIwasawaCompact.height`, the factor `heightPower` (`m_P(g)^λ`) and the twist
`parameterTwist` (`φ_λ = φ m_P^λ`) (modules `AdelicIwasawaHeight`, `AdelicEisensteinSeries`).
It also proves finiteness of rational characters of parabolics.

## Heights (namespace `Langlands.Global.AdelicGroupPoints`)

- `IsIwasawaCompact.isClosedMap_mul`: for `P(𝔸) K = G(𝔸)` with `K` compact, the map
  `P(𝔸) × K → G(𝔸)`, `(x, k) ↦ p(x) k` is closed. It factors as the closed embedding
  `p × id` (the Library's `isClosedEmbedding_map`), the homeomorphism `(y, k) ↦ (y k, k)` of
  `G(𝔸) × K`, and the projection to `G(𝔸)`. The projection is closed because `K` is compact.
- `IsIwasawaCompact.continuous_height`: `H_P` is continuous. The map above is a continuous closed
  surjection, hence a quotient map. `H_P` composed with it is `log_P ∘ pr₁` (`height_eq`), which
  is continuous (`continuous_characterLog`).
- `continuous_complexParameterPairing`, `IsIwasawaCompact.continuous_heightPower`,
  `IsIwasawaCompact.continuous_parameterTwist`: hence `g ↦ m_P(g)^λ` is continuous, and so is
  `φ_λ` for continuous `φ`. The first is proved by induction on the tensor `λ`.
- `complexParameterPairing_parameterRestrict`: `⟨λ ∘ f, H⟩ = ⟨λ, f_* H⟩` for `f : P' → P`.
- `IsIwasawaCompact.height_eq_realCharacterDualMap`: if `K` is an Iwasawa subgroup for
  `f ≫ p : P' → G`, then `H_P = f_* ∘ H_{P'}`. Write `g = p(f(x)) k` and use `characterLog_map`.
- `IsIwasawaCompact.heightPower_restrict`: twist matching,
  `m_{P'}(g)^{parameterRestrict f λ} = m_P(g)^λ`.
- `IsIwasawaCompact.heightPower_unipotent_mul`, `IsIwasawaCompact.heightPower_rational_mul`:
  `m_P^λ` is left invariant under the adelic points of a unipotent subgroup of `P` and under
  `P(F)`. They follow from the Library's `height_unipotent_mul` and `height_rational_mul`.

## Character lattices (namespace `Langlands.GroupScheme`)

- `rationalCharacters_free_finite`: over a field, the rational characters of a smooth
  connected affine group scheme form a free `ℤ`-module of finite rank. The proof is the
  Library's proof of `rationalCharacterLattice`
  (`Langlands/GroupScheme/Rational/CharacterLatticeProof.lean`), copied verbatim with the
  connected reductive hypothesis replaced by the three properties that proof uses
  (`IsAffineHom`, `Smooth`, `ConnectedSpace`).
- `IsParabolicSubgroup.finite_rationalCharacters`: for a parabolic `P` of a connected reductive
  `G`, `X^*(P)` is finitely generated. `P` is smooth (`IsParabolicSubgroup.smooth`) and
  connected (Library `IsParabolicSubgroup.connectedSpace`).

## Coordinates (namespace `Langlands.Global.AdelicGroupPoints`)

- `exists_complexParameterEquiv`: for such `P` there is a linear equivalence
  `(Fin n → ℂ) ≃ₗ[ℂ] X^*(P) ⊗ ℂ`. It is the coordinate map of a basis of the finite-dimensional
  space. The published `EisensteinAbsoluteConvergenceStatement` quantifies over such
  coordinate systems, and this lemma lets it be applied at a single parameter.

## Provenance

The equality `m_{P_w}(x)^{λ|} = m_P(x)^λ` and the restriction `X_P ⊆ X_{P_w}` are those of
Bernstein–Lapid §6.10, first sentence (journal p. 208, PDF page 22), recorded in the target
statement's Markdown. Continuity of the height and finiteness of `X^*(P)` are standard; the
formalization is internal.

The continuity of the Iwasawa height uses the theorem in `AdelicEisensteinCompactBounds`.
