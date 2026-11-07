# Rank-one factors of the local virtual identity on the original fields

This module continues `RelativeWeilLocalEpsilon`. That module computes the arithmetic pair
epsilon value of a local virtual identity

`[T] = d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`, `T ≃ V ⊗ W`,

for a supplied common-closure local-constant system `(eC, ε, hε)` of a p-adic field `F`.
It expresses the value through abelian epsilon expressions on intermediate fields of
the common closure: the bottom field `⊥` and the images `L_j` of the standalone
extensions `E_j`. This module moves each factor to Tate's fixed-Haar epsilon factor
`PadicAbelian.epsilon` on the original field, `F` or `E_j`, at the same spectral
parameter `s`.

## Provenance

The provenance is derived. The rank-one factors are Tate's local epsilon factors of
quasicharacters, *Number theoretic background* (Corvallis 1979), §3.2, printed
pp. 13–14 (PDF pp. 22–23), in the
Library's form `PadicAbelian.epsilon`. In Theorem (3.4.1), printed pp. 14–15, the
quasicharacter of a degree-one representation is read through the reciprocity law.
Here that law is the system's own reciprocity family `eC`, transported to the original
fields. All other content is internal bookkeeping that composes published Library
results: the field isomorphisms `⊥ ≃ F` and `E ≃ L`, transport of abelian epsilon
expressions along them (`AbelianTransport.abelianEpsilonExpression_eq`), the bottom-field
lemmas of `Correspondence.RankOneEpsilonFieldTransport` and `RankOneNormalizedEpsilon`,
and `PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul`, which identifies the
abelian expression of `|·|^s χ` with `PadicAbelian.epsilon χ s`.

## Declarations (`Langlands.Weil.Local.SystemEpsilon`)

- `baseFactor_eq_epsilon`: the setting is a normalized family `eC`, a quasicharacter
  `χ` of `F`, and the Weil character `RankOne.weilCharacter F (baseReciprocityCandidate F
  eC) χ`, whose candidate is the bottom component of `eC` transported to `F`. For a
  bottom-field additive character `ψ` with `IsBaseCharacter F ψF ψ` and any Haar measure
  `μ` on `⊥`, the bottom-field factor equals
  `PadicAbelian.epsilon F χ ψF ((baseFieldHaarMeasureEquiv F).symm μ).measure s`.
- `weilCharacter_imageQuasicharacter`: let `η` be a quasicharacter of `E` and `rec` be
  `LocalClassField.extensionReciprocityCandidate F E g eC`, the component of `eC` at
  the image `L` of `E`, transported to `E`. Transport the quasicharacter `|·|_E^s η` to
  `L` by the field isomorphism. Its Weil character for `eC` is
  `CommonClosureSpectral.character F L s * imageCharacter F E g (η ∘ rec)`. The proof
  evaluates at elements `extensionImageWeilEquiv v` and uses the normalization of
  `eC` (`CommonClosureSpectralAnalytic.character_eq_norm_exp`) and the preservation of
  normalized absolute values by the field isomorphism.
- `imageFactor_eq_epsilon`: for an additive character `ψE` and a Haar measure `μE` on
  `E`, transported to `L` (`CommonClosureSystemTransport.imageAdditiveCharacter`,
  `imageHaarMeasure`), the factor of the image of `E` for the character `η ∘ rec`
  equals `PadicAbelian.epsilon E η ψE μE.measure s`.
- `standaloneTraceCharacter F E g ψF`: the additive character `ψF ∘ Tr_{E/F}` of `E`,
  where `E` is an `F`-algebra through `g`.
- `botEquiv_trace_eq`: under `⊥ ≃ F` and `E ≃ L`, the trace of `L/⊥` is the trace of
  `E/F`. The proof is Mathlib's `Algebra.trace_eq_of_equiv_equiv`.
- `traceCharacter_eq_imageAdditiveCharacter`: for `IsBaseCharacter F ψF ψ`, the
  trace character from `⊥` to `L` used by the system's induction relation is the
  transport of `standaloneTraceCharacter F E g ψF`.
- `conditionalPairEpsilonValue_eq_epsilon_of_virtualIdentity` (main theorem). The
  setting is the virtual identity with `α₀ = χ₀ ∘ rec_F` and
  `α_j = η_j ∘ rec_{E_j}`, `β_j = η'_j ∘ rec_{E_j}`, where `rec_F` is
  `baseReciprocityCandidate F eC` and `rec_{E_j}` is
  `extensionReciprocityCandidate F E_j g_j eC`. Then, for every admissible bottom-field
  datum `(ψ, μ, A, B, Φ)` with `IsBaseCharacter F ψF ψ`, every family of Haar measures
  `μE j` on the `E_j`, and every `s`, the conditional pair epsilon value equals

  `ε_F(χ₀, ψF, μF, s)^d · Π_j (ε_{E_j}(η_j, ψF ∘ Tr, μE j, s) /
  ε_{E_j}(η'_j, ψF ∘ Tr, μE j, s))^{n_j}`,

  where `ε = PadicAbelian.epsilon` and `μF = (baseFieldHaarMeasureEquiv F).symm μ`.
  The proof applies `RelativeWeilLocalEpsilon`'s theorem with the measures
  `imageHaarMeasure (μE j)` on the images, then the lemmas above. The normalization
  `hε.1` of the system is used.

## Scope

The reciprocity maps `rec_F` and `rec_{E_j}` are those of the supplied family `eC`.
Comparing them with geometric reciprocity candidates
(`LocalClassField.GeometricWeilReciprocityRelation`), as the local components of Hecke
characters require, is not done here.
