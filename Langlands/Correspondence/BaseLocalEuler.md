# Restriction of local pairs to the bottom intermediate field

Author: Worker 1695.

This module compares local Weil–Deligne pairs over `F` with their restrictions
to the bottom intermediate field `⊥ = baseExtension F` of the common closure. It
supplies the base-to-local Euler polynomial comparison and the identifications of
restricted blocks and twisted factors used in
`Langlands.Correspondence.SegmentGaloisGamma` and
`Langlands.Correspondence.SegmentEpsilonInheritance`. Everything is proved
unconditionally from published definitions, with only the standard axioms.

Throughout, `F : PadicField.{uF} p` with `[Fact p.Prime]`, `ω` is the local norm
character `(localNormCharacter F).toMonoidHom`, and the restriction is along the
subtype of `weilSubgroup F (baseExtension F)`.

## Restriction and operations (namespace `Langlands.WeilDeligneRepresentation`)

The underlying linear map of each equivalence is the identity.

- `restrictTensorEquiv φ A B`: `restrict φ (A ⊗ B) ≅ restrict φ A ⊗ restrict φ B`.
- `restrictBlockEquiv φ A m`: the restriction of the uncentered block
  `block ν A m` is `block (ν ∘ φ) (restrict φ A) m`.
- `restrictDualEquiv φ A`: `restrict φ (A^∨) ≅ (restrict φ A)^∨`. The proof
  uses `φ (h⁻¹) = (φ h)⁻¹`.

Tensor products of equivalences use the published
`WeilDeligneRepresentation.tensorCongr` of `RankOneArithmeticLFactor`.

## Residue cardinality and Frobenius (namespace `Langlands.Correspondence`)

- `baseResidueCardinality_eq`: the residue cardinality of `⊥` in the
  common-closure field data equals `F.canonicalTopologicalData.residueCardinality`.
  The proof applies `PadicField.CanonicalTransport.residueCardinality_eq` to the
  `ℚ_p`-algebra isomorphism `F ≃ ⊥` obtained from `IntermediateField.botEquiv`.
  The proof uses the algebra structure of `asPadicField`.
- `baseResidueCardinality_real`: the same equality for the real residue
  cardinality `residueCardinality F (baseExtension F)`.
- `baseGeometricFrobenius`: the image of the published `localGeometricFrobenius F`
  under `baseWeilEquiv F` is a geometric Frobenius over `⊥`. Its norm-character
  value is `q⁻¹` by `localNormCharacter_geometricFrobenius` and
  `baseResidueCardinality_eq`.

## Euler polynomials

- `eulerPolynomial_base_of_equiv B₀ A f Φ`: if `f` is an equivalence from the
  restriction of a local pair `B₀` to a pair `A` over `⊥`, then for every
  geometric Frobenius `Φ` over `⊥` the Euler polynomial of `A` at
  `(inertia F ⊥, Φ)` equals the local Euler polynomial of `B₀` at
  `(localInertia F, localGeometricFrobenius F)`. The proof has three steps:
  - Frobenius independence over `⊥`: `CommonClosureGamma.eulerPolynomial_eq_of_frobenius`,
    passing from `Φ` to `baseGeometricFrobenius F`.
  - Invariance under the equivalence `f`: `WeilDeligne.eulerPolynomial_eq_of_equiv`.
  - Transport along the group isomorphism `(baseWeilEquiv F).symm`:
    `WeilDeligne.Transport.eulerPolynomial_restrict`.
- `eulerPolynomial_dual_base_of_equiv`: the same statement for the duals, through
  `restrictDualEquiv` and `dualEquiv`.

## Lifted restrictions

- `baseLift F B`: for a local Weil representation `B` with carrier in `uP`, the
  restriction of `B` to the Weil group of `⊥`, with its carrier lifted by
  `universeLiftRepresentation` to `max uF uP`. This is the universe of
  common-closure pairs required by `PairBlock.BlockPairGamma`.
- `baseLiftEquiv`: the lift is equivalent to the restriction.
- `baseLift_isContinuous`: the lift of a continuous representation is continuous.
- `isContinuous_of_classOf_eq`: a representative of the forgotten class of an
  irreducible Weil class is continuous.
- `restrictBlockBaseEquiv B m`: the restriction of the local block `block ω B m`
  is equivalent to `block (normCharacter F ⊥) (baseLift F B) m`. It combines
  `restrictBlockEquiv` with `Blocks.blockEquivAcross`.
- `restrictTwistedBaseEquiv B k`: the restriction of the zero-monodromy pair of
  `ω^k B` is equivalent to `twistedFactor F ⊥ (baseLift F B) k`.
- `restrictZeroBaseEquiv B`: the restriction of the zero-monodromy pair of `B` is
  equivalent to `twistedFactor F ⊥ (baseLift F B) 0`. The proof composes
  `restrictTwistedBaseEquiv B 0` with the identification `B ≅ ω^0 B`, given by
  `twistEquivOfEq (pow_zero _)` and `twistOneEquiv`.
- `restrictTwistedPairBaseEquiv B B' k`: the restriction of
  `zm(ω^k B) ⊗ zm(B')` is equivalent to
  `twistedFactor F ⊥ (baseLift F B ⊗ baseLift F B') k`, by `twistedPairEquiv` with
  exponents `k` and `0`.

## Provenance

These are derived comparison lemmas. They contain no new mathematical claim
beyond the published definitions of restriction, blocks, twisted factors and
Euler polynomials.
