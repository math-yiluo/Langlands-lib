# Twisted pair L compatibility of supercuspidal correspondences

Author: Worker 1706.

This module proves the premise `SupercuspidalTwistedPairLInheritance` of module
`AssemblyLSegmentReduction`. Every supercuspidal correspondence `c0` is compatible
with pair L-factors after the first factor is twisted by `ν^x`, `x ∈ ℕ`. The
module then removes that premise from the reduction of
`Langlands.Correspondence.AssemblyLInheritanceStatement`.

The proof is unconditional. It uses only the fields of
`IsSupercuspidalCorrespondence`. **The target statement is still not proved
here.** The final theorem keeps the other five premises of
`AssemblyLSegmentReduction.assemblyLInheritance_of_segmentHeads` as hypotheses.

All declarations are in namespace `Langlands.Correspondence`. Throughout,
`F : PadicField.{uF} p` and `[Fact p.Prime]`. Notation:

- `ω` is `Weil.Local.localNormCharacter F`, the norm character of the Weil group.
- `|·|` is `F.canonicalTopologicalData.normalizedAbs`.
- `rec_e` is `LocalFactor.RankOne.reciprocityUnits F e`, the map from the Weil
  group to `F^×` given by a reciprocity candidate `e`.

## Definition

### `normPowerQuasiCharacter F e x`

```lean
def normPowerQuasiCharacter (e : ReciprocityCandidate F) (x : ℕ) : QuasiCharacter F :=
  LocalFactor.RankOne.fieldCharacter F e (Weil.Local.localNormCharacter F ^ x)
```

This is the field quasi-character that corresponds to `ω^x` under the published
character transport `fieldCharacter` along `e`. It is an internal construction.
When `e` is geometrically normalized it is `|·|^x`; see
`normPowerQuasiCharacter_apply` below.

## Theorems

- `localNormCharacter_eq_normalizedAbs (he : IsGeometricReciprocity F e) w`:
  `ω w = |rec_e w|` in `ℂ`. Proof: the first conjunct of `IsGeometricReciprocity`
  says that the valuation of `rec_e w` is the degree `localDegreeInt F w`. Then
  `localNormCharacter_apply` gives `ω w = q^(-deg w)`, and `normalizedAbs_of_ne_zero`
  gives `|a| = q^(-ord a)`.
- `reciprocityUnits_surjective e`: `rec_e` is surjective. It is the quotient map
  to the abelianization followed by the equivalence `e`.
- `weilCharacter_normPowerQuasiCharacter e x`:
  `LocalFactor.RankOne.weilCharacter F e (normPowerQuasiCharacter F e x) = ω^x`.
  This is the published `weilCharacter_fieldCharacter`.
- `normPowerQuasiCharacter_apply (he : IsGeometricReciprocity F e) x a`:
  `normPowerQuasiCharacter F e x a = |a|^x` in `ℂ` for every `a : F^×`. Proof:
  write `a = rec_e w` by surjectivity. Then the value is `(ω^x) w = (ω w)^x`,
  which equals `|a|^x` by the first theorem.
- `determinantQuasiCharacter_normPowerQuasiCharacter (he : IsGeometricReciprocity F e) x n`:
  `determinantQuasiCharacter F n (normPowerQuasiCharacter F e x)` is
  `F.canonicalTopologicalData.determinantPowerCharacter n x`, the character
  `g ↦ |det g|^x` of `GL_n(F)`. Proof: compare values by extensionality and use
  the previous theorem at `det g`.
- `weilPairClass_eq_classOf σ B hB`: if `B` represents the irreducible Weil class
  `σ`, then `weilPairClass F σ` is the class of `zeroMonodromy ω B`. This holds by
  unfolding `weilPairClass`, which is defined by `Quotient.map`.

### Main theorem

```lean
theorem IsSupercuspidalCorrespondence.twistedSupercuspidalPairLCompatibility
    {c0 : SupercuspidalMap.{uF, uP, uA} F} (hc0 : IsSupercuspidalCorrespondence F c0) :
    TwistedSupercuspidalPairLCompatibility F c0
```

This is the proof as implemented. Destructure `hc0`. This gives a geometrically
normalized candidate `e` (`he`), twist compatibility `htw`
(`SupercuspidalTwistCompatibility F e c0`), and factor compatibility. From the
factor compatibility we get a system `eC, ε, hε` and pair compatibility `hpair`
(`SupercuspidalPairFactorCompatibility`). Now fix the data of
`TwistedSupercuspidalPairLCompatibility`:

- a nontrivial `ψ` and a self-dual `ν`;
- `σ` of rank `d + 1` with representative `B`, and `τ` of rank `t + 1` with
  representative `B'`;
- supercuspidal representatives `A` of `c0 σ` and `A'` of `c0 τ`;
- `x : ℕ`.

The proof has five steps.

1. Let `χ = normPowerQuasiCharacter F e x`. By the determinant theorem, `χ ∘ det`
   is `|det|^x` on `GL_(d+1)(F)`. That character has open kernel by
   `isOpen_ker_determinantPowerCharacter`.
2. Let `σ'` be the published certified twist
   `FiniteRepresentation.continuousIrreducibleTwistEquiv (weilCharacter F e χ) (d + 1) σ`.
   Twist compatibility `htw (d + 1) σ χ` and the published
   `isSupercuspidalCharacterTwist_iff_eq_twist` give
   `c0 σ' = (twist (χ ∘ det) A).isoClass`; here `hA : A.isoClass = c0 σ` was
   rewritten backwards.
3. `hpair ψ d t σ' τ`, at the self-dual `ν`, gives `P : ℂ[X]` and two facts:
   - `IsSupercuspidalPairLPolynomial F ψ ν (c0 σ') (c0 τ) P`;
   - the arithmetic pair L-factor of `weilPairClass σ'` and `weilPairClass τ` is
     `(algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹`.

   Rewrite `c0 σ'` and `c0 τ` with the representatives from step 2 and `hA'`.
   `IsSupercuspidalPairLPolynomial` is a `Quotient.lift₂`, so on these classes it
   reduces to
   `IsPadicSymmetricLPolynomial F ψ ν (twist (χ ∘ det) A) A' P`.
   Rewriting `χ ∘ det` by step 1 gives the analytic conjunct, since
   `realPowerTwist (determinantNorm (d + 1)) x` is the twist by
   `determinantPowerCharacter (d + 1) x`.
4. As monoid homomorphisms, `weilCharacter F e χ = ω^x`. This follows from
   `weilCharacter_normPowerQuasiCharacter` and `ContinuousMonoidHom.pow_apply`.
   So `twist (ω^x) B` represents `σ'`. The proof uses
   `forget_continuousIrreducibleTwistEquiv`, `hσ` and `twistClass_classOf`.
5. Apply `weilPairClass_eq_classOf` to `σ'` with `twist (ω^x) B`, and to `τ` with
   `B'`. This turns the arithmetic identity of step 3 into the arithmetic conjunct
   of the conclusion, for the zero-monodromy representations of `ω^x B` and `B'`.

Every step holds for every `x : ℕ`, every nontrivial `ψ` and every self-dual `ν`.
No premise is added.

### Packaging

```lean
theorem supercuspidalTwistedPairLInheritance :
    SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F

theorem assemblyLInheritance_of_segmentHeads_of_blockPairs
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F
```

The first theorem applies the main theorem to every supercuspidal correspondence.
The second passes it as the last premise of `assemblyLInheritance_of_segmentHeads`.
Its five hypotheses are the premises of the target that are still open. They are:

- datum existence for multisegment heads;
- JPSS (9.5) in product form;
- arithmetic multiplicativity of pair L-factors over direct sums;
- the segment-head L formula of Henniart 2002, §2.6;
- the arithmetic block-pair formula.

## Provenance

The module is derived. It contains no new literature claim. It proves the twisted
identity `L(s, ν^x π_0(ρ) × π_0(ρ')) = L(s, ν^x ρ ⊗ ρ')`, which Henniart 2002,
§2.7 (printed p.595, PDF p.9) uses when it compares the products of §2.4 and
§2.6. The proof combines the Library's twist compatibility for the character
`|·|^x` with its pair-factor compatibility for supercuspidal correspondences.
`normPowerQuasiCharacter` is internal infrastructure. It is the character `|·|^x`,
built by transporting `ω^x` along the reciprocity candidate.
