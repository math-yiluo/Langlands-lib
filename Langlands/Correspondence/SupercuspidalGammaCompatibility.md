# Derived gamma compatibility of supercuspidal families

Author: Worker 7. This module defines the pair gamma factor on both sides of
the irreducible-Weil to supercuspidal correspondence, states the gamma
compatibility of a supercuspidal map, and states, as a proposition only, that
gamma compatibility follows from the pair L-, epsilon- and dual conditions.
Nothing is proved except the well-definedness of the class-level relation, and
no family, character, measure or local-constant system is chosen.

## Definitions

`F : PadicField p` carries its canonical topological data, `q` is its residue
cardinality, and factors are rational functions of `X = q^(-s)`.

- `LocalFactor.residueReflection F`, imported from
  `LocalFactor/ResidueReflection`, is the published unit
  `WeilDeligne.reflectionScale q = q⁻¹`. The published
  `spectralParameter_one_sub` shows that `s ↦ 1 - s` is `X ↦ q⁻¹/X`. The
  positivity of `q` comes from the published `residueCardinality_gt_one`.
- `IsArithmeticPairGammaFactor F eC ε hε ψ X Y G`, for pair classes `X`, `Y`
  of the local Weil group (`LocalPairClass` of `ArithmeticFactors`): there are
  `c : ℂˣ` and `m : ℤ` such that `IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y c m`
  holds and
  `G = c X^m · L((X ⊗ Y)^∨)(q⁻¹/X) / L(X ⊗ Y)(X)`.
  The ratio is the published `WeilDeligne.rationalLRatioClass` of the actual
  tensor class (`tensorClass`), at the published inertia subgroup and
  geometric Frobenius lift. The dual is the published Weil–Deligne dual with
  monodromy `-Nᵀ`. The monomial is the published
  `RankinSelberg.rationalEpsilonMonomial c m`.
- `IsSupercuspidalPairGammaFactor F ψ ν π τ G`, for supercuspidal classes of
  ranks `r + 1` and `n + 1`, is Worker 11's published
  `RankinSelberg.IsPadicSymmetricGammaFactor` on representatives: the JPSS
  gamma relation with the representation of larger rank as candidate (in equal
  rank, `π`). It is defined with `Quotient.lift₂`; independence of the
  representatives is proved from the published `congr_equiv` lemma, as for the
  L and epsilon relations of `SupercuspidalFactorCompatibility`.

## Conditions

`SupercuspidalPairGammaCompatibility F eC ε hε c`: for every nontrivial
unitary additive character `ψ`, all `r n : ℕ`, and irreducible Weil classes `σ`
of rank `r + 1` and `τ` of rank `n + 1`, a measure self-dual for `ψ` exists,
and for every self-dual `ν` some `G` satisfies both
`IsSupercuspidalPairGammaFactor F ψ ν (c σ) (c τ) G` and
`IsArithmeticPairGammaFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ) G`.
The witness `G` is asserted to exist, so the condition implies that the JPSS
gamma factor of every image pair exists.

`SupercuspidalGammaCompatibility F e c` existentially quantifies a system
`(eC, ε, hε)` with `IsBaseReciprocity F e eC`, exactly as
`SupercuspidalFactorCompatibility` does.

`SupercuspidalGammaFromFactorsStatement F` says: for every reciprocity family
`eC`, system `ε` with `hε : IsSystem F eC ε`, and supercuspidal map `c`, if
`SupercuspidalPairFactorCompatibility F eC ε hε c` and
`SupercuspidalDualCompatibility F c` hold, then
`SupercuspidalPairGammaCompatibility F eC ε hε c` holds, for the same system
and the same map. It is a statement, not a theorem; the Library contains no
proof of it. The intended proof applies the L condition to the duals
`σ^∨`, `τ^∨`, uses dual compatibility to identify their images with the
contragredients of `c σ` and `c τ`, and then uses the JPSS functional
equation to identify the JPSS gamma factor with
`ε L(1 - s, π^∨ × τ^∨)/L(s, π × τ)`. That last identification is not proved
in the Library.

The other comparison this route needs is proved. The published Rankin–Selberg
modules use the inverse-transpose pullback `g ↦ π(ᵗg⁻¹)`, while dual
compatibility uses the actual smooth contragredient. The published theorem
`Langlands.gelfandKazhdanContragredient` proves that, for an irreducible
admissible representation of `GL_(n+1)(F)`, the two are equivalent.
`RankinSelberg/SmoothDualPairFactors` turns this into the chosen equivalence
`RankinSelberg.inverseTransposeSmoothDualEquiv`. It also proves
`RankinSelberg.isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient`
and its epsilon and gamma analogues: each symmetric L, epsilon or gamma relation
of two irreducible admissible representations holds for their inverse-transpose
pullbacks exactly when it holds for their smooth contragredients. This module
does not import these results.

## Sources and provenance

- Henniart 2000, §1.2, remark after property 4), printed p.440 (PDF p.2):
  `γ(σ ⊗ σ', s, ψ) = ε(σ ⊗ σ', s, ψ) L(σ^∨ ⊗ σ'^∨, 1 - s)/L(σ ⊗ σ', s)`,
  likewise `γ(π × π', s, ψ)`, "et on a bien sûr alors une identité évidente
  (4γ)". The derived statement is this remark.
- Henniart 2002, §1.2, printed p.589 (PDF p.3): the same definition of `γ`
  for Weil–Deligne representations and for pairs `π × π'`.
- The representation-side gamma relation and its JPSS source (Theorem 2.7,
  (2.12)) and the Henniart 1993 definition (2.3.4) are recorded in the
  published `RankinSelberg/GammaFactor` and `RankinSelberg/PadicPairFactors`.

Source files:

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Interpretation

- Gamma compatibility is not a substitute for the separate L and epsilon
  conditions. It is weaker and is stated only as a consequence.
- Both sides use the same rational variable `X = q^(-s)` and the same
  reflection `X ↦ q⁻¹/X`.
- `IsArithmeticPairGammaFactor` is a relation because the arithmetic epsilon
  factor is a relation. Different witnesses `(c, m)` give the same `G`
  whenever the epsilon relation determines `(c, m)`; this uniqueness is not
  needed for the statements here.

The module imports, and does not copy: `LocalFactor.WeilDelignePair`
(`rationalLRatioClass`), `LocalFactor.ResidueReflection` (`residueReflection`), `WeilDeligne.SumsTensor`
(`tensorClass`), `RankinSelberg.PairEpsilonFactor`
(`rationalEpsilonMonomial`), `RankinSelberg.PadicPairFactors`
(`IsPadicSymmetricGammaFactor` and its `congr_equiv`), and this task's
`ArithmeticFactors`, `SupercuspidalFactorCompatibility` and
`OperationCompatibility`.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every definition in this module returns `Prop`; the imported reflection
scalar is documented in `LocalFactor/ResidueReflection`.
