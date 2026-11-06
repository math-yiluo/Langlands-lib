# Supercuspidal gamma compatibility from L, epsilon and duality: proof

Author: Worker 1697.

The theorem `Langlands.Correspondence.supercuspidalGammaFromFactors` proves the
unchanged Library proposition
`Langlands.Correspondence.SupercuspidalGammaFromFactorsStatement.{uF, uP, uA} F`
for every prime `p` with `[Fact p.Prime]` and every `F : PadicField.{uF} p`.
The proposition is stated in `Correspondence/SupercuspidalGammaCompatibility`.

The proof keeps the statement's hypotheses and adds none. For every reciprocity
family `eC`, local-constant assignment `ε`, system proof `hε` and supercuspidal
map `c`, it assumes `SupercuspidalPairFactorCompatibility F eC ε hε c` and
`SupercuspidalDualCompatibility F c`. It then proves
`SupercuspidalPairGammaCompatibility F eC ε hε c` for the same system and map.
This holds for every nontrivial `ψ`, all ranks `r + 1` and `n + 1`, all
irreducible Weil classes `σ` and `τ`, and every self-dual measure `ν`. The proof
has no JPSS functional equation hypothesis and no inverse-transpose or
smooth-dual comparison hypothesis. These inputs come from published Library
theorems, named below. Lean reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The gamma witness

Fix `ψ`, `r`, `n`, `σ` and `τ`. The pair-factor hypothesis at `(ψ, σ, τ)`
supplies a measure that is self-dual for `ψ`. This is the first conjunct of the
goal. Now fix a measure `ν` that is self-dual for `ψ`. At `ν`, the hypothesis
supplies two things:

- a polynomial `P` such that `IsSupercuspidalPairLPolynomial F ψ ν (c σ) (c τ) P`
  holds and `arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) = P⁻¹`;
- a pair `e = (c₀, m)` that is both the JPSS epsilon factor of `(c σ, c τ)` and
  the arithmetic epsilon factor `IsArithmeticPairEpsilonFactor F eC ε hε ψ …`.

Write `σ^∨` and `τ^∨` for the published duals
`FiniteRepresentation.continuousIrreducibleDualEquiv` of `σ` and `τ`. Let
`ψ⁻ = ψ.scale (-1)` be the character `x ↦ ψ(-x)`. The same `ν` is self-dual for
`ψ⁻`: this is the published `IsSelfDual.scale_neg_one`, used through
`DominantRankTransport.negatedSelfDualHaar`. The pair-factor hypothesis at
`(ψ⁻, σ^∨, τ^∨, ν)` supplies a polynomial `P'` such that
`IsSupercuspidalPairLPolynomial F ψ⁻ ν (c σ^∨) (c τ^∨) P'` holds and
`arithmeticPairLFactor F (weilPairClass F σ^∨) (weilPairClass F τ^∨) = P'⁻¹`.

The witness is
`G = rationalGammaExpression (residueReflection F) c₀ m P P'`, that is,
`G(X) = c₀ X^m P(X) / P'(q⁻¹/X)`.

## Representation side: `IsSupercuspidalPairGammaFactor F ψ ν (c σ) (c τ) G`

1. *Representatives.* Choose supercuspidal representatives `Aσ`, `Aτ`, `Aσ'`
   and `Aτ'` of `c σ`, `c τ`, `c σ^∨` and `c τ^∨`. On representatives, every
   class-level relation in the hypotheses and in the goal is the corresponding
   `IsPadicSymmetric…` relation, because it is defined by `Quotient.lift₂`.
2. *Duality.* `exists_equiv_of_isSupercuspidalSmoothDual` unfolds
   `IsSupercuspidalSmoothDual` and uses the published `automorphicClassOf_eq_iff`.
   It gives an irreducible admissible representation `Bσ` with `Bσ ≃ Aσ` and
   `smoothContragredient Bσ ≃ Aσ'`. The same lemma gives `Bτ` for `τ`.
3. *Genericity.* The pair-factor hypothesis also covers the equal-rank pair
   `(σ, σ)`, which gives an epsilon relation for `(c σ, c σ)`. By the definition
   of `IsEqualRankEpsilonFactor`, an equal-rank epsilon relation contains a
   nonzero standard Whittaker functional. With irreducibility and admissibility,
   this is `Whittaker.IsGeneric ψ r`
   (`RankinSelberg.isGeneric_of_isPadicSymmetricEpsilonFactor_self`). The
   relation is first transported to `Bσ` by `congr_equiv`. The same argument
   with `(τ, τ)` makes `Bτ` generic.
4. *Gamma expression.* `RankinSelberg.isPadicSymmetricGammaFactor_of_smoothDual`
   takes the following inputs:
   - generic `π` and `σ`;
   - equivalences `smoothContragredient π ≃ π'` and `smoothContragredient σ ≃ σ'`;
   - the epsilon relation `e` and L-relation `P` of `(π, σ)`;
   - the L-relation `P'` of `(π', σ')` for `ψ⁻`.

   It proves `IsPadicSymmetricGammaFactor F ψ ν π σ (rationalGammaExpression … P P')`.
   The published Gelfand–Kazhdan comparison
   `isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient`
   rewrites `P'` as the L-polynomial of the inverse-transpose pullbacks. The
   published `symmetricGammaExpression` then yields the gamma factor. Its
   construction input is the published `genericSymmetricGammaConstructionInput`,
   which carries the JPSS functional equation for generic pairs.
5. *Transport.* The relations at `(Aσ, Aτ)` move to `(Bσ, Bτ)`, and the gamma
   relation moves back, by `IsPadicSymmetric….congr_equiv`.

## Arithmetic side: `IsArithmeticPairGammaFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ) G`

The epsilon witness is `(c₀, m)`, with the arithmetic relation from the
hypothesis. It remains to prove
`G = c₀ X^m · rationalLRatioClass … (tensorClass (weilPairClass F σ) (weilPairClass F τ))`.

- The shared `WeilDeligneRepresentation.tensorDualEquiv A B` in
  `Langlands/WeilDeligne/TensorDual` is a genuine pair equivalence
  `tensor (dual A) (dual B) ≃ dual (tensor A B)`. Its underlying linear map is
  Mathlib's `TensorProduct.dualDistribEquiv`, `l ⊗ m ↦ (x ⊗ y ↦ l x · m y)`.
  The lemma `dualDistribEquiv_comp_map_dualMap` shows that it intertwines the
  dual actions, which are transposes of `g⁻¹`. The lemma
  `dualDistribEquiv_comp_monodromy` shows that it intertwines the monodromies
  `-Nᵀ ⊗ 1 + 1 ⊗ -N'ᵀ` and `-(N ⊗ 1 + 1 ⊗ N')ᵀ`. On classes this gives
  `dualClass_tensorClass`.
- `dualZeroMonodromyEquiv` identifies the dual of a zero-monodromy pair with the
  zero-monodromy pair of the dual representation, by the identity map. With the
  published `forget_continuousIrreducibleDualEquiv`, this gives
  `weilPairClass_continuousIrreducibleDualEquiv`:
  `weilPairClass F σ^∨ = dualClass (weilPairClass F σ)`.
- `LocalFactor.WeilDeligne.rationalLRatioClass_eq` holds by definition. The
  class-level reflected ratio is `subst δ (L(dual X)) / L(X)`, where `subst δ`
  is the published substitution `X ↦ δ/X`.
- These combine to `rationalLRatioClass_tensor_weilPairClass`. The ratio for
  `σ ⊗ τ` equals
  `subst δ (arithmeticPairLFactor F (weilPairClass F σ^∨) (weilPairClass F τ^∨)) / arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ)`.

Substitute the two L-conditions `P⁻¹` and `P'⁻¹` and apply `map_inv₀` and
`RationalReflection.subst_polynomial`. The ratio becomes `P(X) / P'(δ/X)`.
Multiplying by the epsilon monomial gives `G`. In both places `δ` is the
published `residueReflection F`, so the two sides use the same reflection.

## Relation to the statement's Markdown

The paired Markdown of the statement says that the identification of the JPSS
gamma factor with `ε L(1 - s, π^∨ × τ^∨) / L(s, π × τ)` is not proved in the
Library. That sentence predates the current Library. The Library now contains
`symmetricGammaExpression` and `genericSymmetricGammaConstructionInput`, and
this proof uses both. The statement's files are not modified.

## Provenance and scope

The statement records its source: Henniart 2000, §1.2, remark after
property 4), printed p.440 (`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`). The remark
defines `γ = ε · L(σ^∨ ⊗ σ'^∨, 1 - s)/L(σ ⊗ σ', s)` on both sides and calls the
gamma identity evident. The implemented proof is an internal derivation from
published Library interfaces. Its analytic content is the JPSS functional
equation, already published through `GammaFromWhittakerType`,
`WhittakerTypeGammaConstructionInputProof`, `PadicGenericGammaFactor` and
`SymmetricGammaExpressionProof`. The Weil–Deligne dual-of-tensor equivalence
and the zero-monodromy comparison are shared in `WeilDeligne/TensorDual` as elementary linear algebra.

The theorem is a conditional implication. It does not assert that any
supercuspidal map satisfies the L, epsilon or dual conditions. It does not
replace those conditions, and it is not the existence of the supercuspidal
correspondence.
