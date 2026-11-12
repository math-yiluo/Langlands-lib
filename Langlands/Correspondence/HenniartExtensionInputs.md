# Standard inputs for extending Henniart's stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionInputs`,
namespace `Langlands.Henniart.Extension`.

This module has two `Prop`-valued definitions and nothing else. Neither is
assumed or proved here. They are hypotheses of
`HenniartConstructionReductionStatement` (module `HenniartExtensionReduction`),
which extends the stable images of Henniart (2000), §4.3, to all irreducible
Weil classes as in Henniart (2000), §4.4. Henniart says this extension follows
"par les arguments (faciles) de [He 4, §4]", that is Henniart (1993), §§4.3–4.4.
The two statements below are the standard facts those arguments use. The field
universe `uK`, Weil carrier universe `uW` and supercuspidal carrier universe `uV`
are independent.

## `SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV}`

For every prime `p`, every `K : PadicField.{uK} p` and every class `π` of the
actual supercuspidal basis `PadicSupercuspidal.Basis.{uK, uV} K` (all positive
ranks), there are a complex unit `z` and a class `π₀` of the unitary
(unitarizable) supercuspidal basis such that:

- the central character of `π₀` has finite order, in the sense of the published
  `Henniart.StableMap.HasFiniteOrderCentralCharacter`;
- `PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val = π`. This is the
  published twist by `g ↦ z ^ ord(det g)`, the determinant composed with the
  unramified character sending the chosen uniformizer to `z`.

Sources.

- Henniart (1993), §4.3, second paragraph, printed p. 349 (PDF p. 11). For a
  supercuspidal `π` of `G_r` and complex `s`, the central character of
  `π ⊗ (|·|^s ∘ det)` is `ω_π |·|^{rs}`, "par suite il existe un nombre complexe
  `s` tel que `π ⊗ (|·|^s ∘ det)` ait un caractère central d'ordre fini".
- Renard (2026), VI.2.1, Théorème (PDF pp. 143–144), VI.2.2 (PDF p. 146) and
  IV.3.2, Lemme (PDF p. 106). A supercuspidal representation has matrix
  coefficients compactly supported modulo the centre. An irreducible
  supercuspidal representation is admissible. An admissible representation that
  is square-integrable modulo the centre, with unitary central character, is
  unitary. A central character of finite order is unitary. This is the fact
  recorded for general reductive groups by the published
  `Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCentralCharacterUnitarizableStatement`.
  It is restated here for the actual `GL_n` class space because the reduction
  consumes it in this form.

Derived form: `π₀ = π ⊗ (|·|^s ∘ det)` and `π = π₀ ⊗ (|·|^{-s} ∘ det)`. The
character `|·|^{-s}` is the unramified character with value `q^s` at a
uniformizer, so `z = q^s`.

## `ArithmeticPairUnramifiedTwistStatement.{uK, uW}`

For every `K`, every common-closure reciprocity family `eC`, every local-constant
assignment `ε : NonabelianSystem.Assignment.{uK, uW} K` with
`NonabelianSystem.IsSystem K eC ε`, every nontrivial additive character `ψ`,
continuous irreducible Weil classes `σ` of dimension `r + 1` and `τ` of
dimension `n + 1`, and complex units `z, z'`, write `σ_z` and `τ_{z'}` for the
published certified twists
`FiniteRepresentation.continuousIrreducibleTwistEquiv` of `σ` and `τ` by
`Weil.Local.localUnramifiedCharacter K z` and `K z'` (the unramified characters
with values `z`, `z'` at geometric Frobenius). Then:

1. if the published arithmetic pair L-factor `arithmeticPairLFactor K
   (weilPairClass K σ) (weilPairClass K τ)` is `1 / P(X)`, then that of
   `(σ_z, τ_{z'})` is `1 / P(z z' X)`, written `(P.comp (C (z z') * X))`;
2. if `IsArithmeticPairEpsilonFactor K eC ε hε ψ (weilPairClass K σ)
   (weilPairClass K τ) c m` (the arithmetic epsilon factor of the pair is
   `c q^(-ms)`), then the same predicate holds for `(σ_z, τ_{z'})` with
   coefficient `c (z z')^m` and the same exponent `m`.

Sources.

- Deligne (1973), (3.5.3), PDF p. 29: with `ω_t` the unramified character with
  `ω_t(F) = t^d` for the geometric Frobenius `F`, `Z(V, t) = L(V ⊗ ω_t)`. Since
  `σ_z ⊗ τ_{z'}` is the twist of `σ ⊗ τ` by the unramified character with value
  `z z'` at geometric Frobenius, its Euler factor `det(1 - X F | V^I)` becomes
  `det(1 - z z' X F | V^I)`.
- Deligne (1973), (5.5.1)–(5.5.2), PDF p. 48: for an unramified quasi-character
  `χ`, `ε(V ⊗ χ, ψ, dx) = ε(V, ψ, dx) χ(π_K^{a(V) + dim(V) n(ψ)})`, and in
  particular `ε(V, ψ, dx, s) = ε(V, ψ, dx) q^{-(a(V) + dim(V) n(ψ)) s}`. Hence if
  the factor at `s` is `c q^{-ms}`, the factor of the twist by the unramified
  character with value `t` at geometric Frobenius (that is, `|·|^{s₀}` with
  `t = q^{-s₀}`) is `c q^{-m(s + s₀)} = c t^m q^{-ms}`, with `t = z z'`.
- Henniart (1993), §4.4, printed p. 349 (PDF p. 11), uses exactly these
  "propriétés élémentaires des facteurs ε (cf. [De, §5] et [JPS 2])":
  `ε(σ ⊗ ρ |·|^u, s, ψ) = ε(σ ⊗ ρ, s + u, ψ)`.

Derived form: the twists act on the two members of the pair separately, which
is the form the reduction consumes. The L clause does not depend on the
local-constant system; it is bundled with the epsilon clause for convenience.

## Literature

- `henniart-1993-epsilon-pairs`, SHA-256
  `057967169237036da64c0e5a72c69e8ddfd69176bebade0ef13588de24809763`.
- `renard-2026-representations-groupes-reductifs-padiques` (French version dated
  9 July 2026).
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
- `henniart-2000-simple-proof`, §4.4, printed p. 453 (PDF p. 15), SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
