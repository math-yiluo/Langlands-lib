# Twisting weakly associated representations by Hecke characters

Author: Worker 5137.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
proves the Weil-group half of the argument: if a representation `S` of `W_{E/F}` is weakly
associated with a spectral system `s`, then the twist `(χ ∘ τ_F) ⊗ S` by the character
`reciprocityCharacter c F E χ` attached to a Hecke character `χ` (of any order) is weakly
associated with the system `s` whose spectrum at `v` is multiplied by `χ_v(ϖ_v)`. This is
the unramified local computation behind Henniart (2000), §2.2: at a place where `χ` is
unramified and `E / F` has ramification index one, `χ ∘ τ_F` restricted along a local
relative Weil map is unramified with Frobenius value `χ_v(ϖ_v)`.

Recall that `reciprocityCharacter c F E χ t = (χ (transfer c F E t))⁻¹`.

## `HeckeCharacter.finiteComponent_eq_finiteUniformizerValue`

If `χ` is unramified at `v` (`χ.IsUnramifiedAt v`: trivial on the units of `𝒪_v`) and
`a ∈ F_vˣ` has valuation `exp (-1)`, then `χ_v(a) = χ.finiteUniformizerValue v`, the value
at the canonical uniformizer `ϖ_v`. The canonical uniformizer also has valuation
`exp (-1)` (`uniformizerUnit_zpow_value`, `discreteValuation_padicField`), so `a ϖ_v⁻¹`
is a unit of `𝒪_v`, on which `χ_v` is trivial.

## Values at a place of ramification index one (section `Values`)

Hypotheses: `E / F` Galois, `FundamentalClass.Restriction c` (`h`), `w` above `z` with
ramification index one (`he`), `χ` unramified at `z` (`hχ`) and
`ι : W_{F_z} →ₜ* W_{E/F}` a local relative Weil map for `w` (`hι`).

- `reciprocityCharacter_eq_finiteUniformizerValue`: for every `y ∈ W_{F_z}` of degree
  one, `(χ ∘ τ_F)(ι y) = χ_z(ϖ_z)`. By `exists_transfer_eq_inv_ofAdicCompletion`
  (module `RelativeWeilUnramifiedTransfer`), `transfer (ι y) = [a]_z⁻¹` with
  `v(a) = exp (-1)`; so `(χ ∘ τ_F)(ι y) = χ([a]_z) = χ_z(a)`, which is `χ_z(ϖ_z)` by the
  previous lemma.
- `reciprocityCharacter_localInertia`: `(χ ∘ τ_F)(ι i) = 1` for every `i` in inertia.
  With `y` the geometric Frobenius of `W_{F_z}` (degree one), both `y` and `y · i` have
  degree one, so the previous lemma gives the same value at `ι y` and `ι (y i)`, and
  hence `(χ ∘ τ_F)(ι i) = 1`.

## Twists (section `Twist`)

- `Langlands.Henniart.Extension.eulerPolynomial_smul`: for an endomorphism `A` of a finite-dimensional space and
  `a ∈ ℂ`, the Euler polynomial `det (1 - X · a A)` is the Euler polynomial of `A`
  evaluated at `a X`; both sides are compared by evaluation (`Polynomial.funext`,
  `LocalFactor.eulerPolynomial_eval`).
- `IsUnramifiedMatchAt.twist`: at a place `v` where every place of `E` above `v` has
  ramification index one and `χ` is unramified, an unramified match of `S` with a
  polynomial `P` gives an unramified match of `(χ ∘ τ_F) ⊗ S` with `P (χ_v(ϖ_v) X)`.
  For each local relative Weil map `ι`, inertia acts on the twist by
  `(χ ∘ τ_F)(ι i) · S(ι i) = S(ι i) = 1`, and the twisted Frobenius operator is
  `χ_v(ϖ_v) · S(ι Frob)`, whose Euler polynomial is given by `Langlands.Henniart.Extension.eulerPolynomial_smul`.
- `continuous_reciprocityCharacter_relativeGalois` and `continuous_reciprocityCharacter`:
  `χ ∘ τ_F` is continuous. The Library provides continuity
  (`continuousReciprocityCharacter`) for the topology of `W_{E/F}` built on the
  `relativeGaloisTopology` of `Gal(E/F)`; the second lemma transports it to the Krull
  topology through `krullTopology_eq_relativeGaloisTopology`.
- `IsWeaklyAssociated.twist_scale`: if `S` is weakly associated with `s`, then
  `(χ ∘ τ_F) ⊗ S` is weakly associated with `SpectralSystem.scale χ.finiteUniformizerValue s`.
  Continuity of the twist is `FiniteRepresentation.isContinuous_twist`, the rank is
  unchanged, and on the cofinite set of places where `S` matches `s`, every place above
  has ramification index one (`eventually_ramificationIdx_eq_one`) and `χ` is unramified
  (`HeckeFunctionalEquation.exists_finset_isUnramifiedAt`), the previous lemma together
  with `SpectralSystem.scale_eulerPolynomial` gives the match.

The scalar Euler identity is imported from the shared
[Euler/Scaling module](../../LocalFactor/Euler/Scaling.md).
