# Reducibility of adjacent supercuspidal products over a local field (proof)

## Statement proved

```lean
theorem Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    AdjacentSupercuspidalProductReducibilityStatement.{uF, uV} F T
```

The theorem proves the proposition
`Langlands.AllFieldBZ.Classification.AdjacentSupercuspidalProductReducibilityStatement.{uF,uV}`
of `Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityStatement`,
unchanged and with no further hypotheses, for every field package `F` and every
nonarchimedean local-field structure `T : F.TopologicalData` (any characteristic). For
every positive rank `r` and actual supercuspidal representations `A, B` of `GL_r(F)` with
`B ≅ νA` or `A ≅ νB` (as isomorphism classes, `ν = |det|` with the residue-normalized
absolute value), the binary normalized product
`(T.binaryNormalizedProductFunctor r r).obj (A.obj, B.obj)` is not irreducible. The
universes `uF` (field) and `uV` (carriers of `A` and `B`) are independent.

## Route

The proof is the argument of Zelevinsky 1980, Proposition 1.11(b), printed p.175, in the
form implemented by the p-adic module
`Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof`
(described in its Markdown page). Every field-dependent input is replaced by its version for
an arbitrary nonarchimedean local field, listed in the table below. The family is
`π_s = ν^s ρ₀ × ν^(-s) ρ₀`; the twist `ν^s` of a smooth representation is
`T.determinantPowerTwist`.

1. **Binary product.** `BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks`
   rewrites the binary product of `(A, B)` as the normalized product on the two-block
   shape `Shahidi.twoBlocks r r` of `twoBlockFactors A B`. The theorem
   `twoBlockAdjacentProduct_not_isIrreducible` then treats this product.
2. **Case `A ≅ νB`.** If `A × B` is irreducible, the irreducible product swap
   `irreducibleTwoFactorProductSwap` gives `A × B ≅ B × A`, so `B × A` is irreducible, and the
   case `B ≅ νA` applied to `(B, A)` gives a contradiction.
3. **Case `B ≅ νA`, reduction (`adjacentProduct_not_isIrreducible`).** Real unitarization
   `Langlands.AllFieldBZ.supercuspidalRealUnitarization` gives `t` with `ν^t A` unitarizable.
   Put `ρ₀ = ν^t A` and `C = ν^(1/2 - t) ρ₀`. Then `A ≅ ν^(-1/2) C` and `B ≅ ν^(1/2) C`,
   since real twists compose additively (`determinantPowerTwistTripleIso`,
   `determinantPowerTwistZeroIso`). By `twistedProductCharacterTwist` with
   `χ = |·|^(1/2 - t)`, the product `ν^(-1/2) C × ν^(1/2) C` is the `χ ∘ det` twist of
   `π_(-1/2)`, so `π_(-1/2)` would be irreducible.
4. **Case `B ≅ νA`, analytic core (`unitaryHalfProduct_not_isIrreducible`).** Let `ρ₀` be a
   unitarizable supercuspidal representation of `GL_k(F)` and suppose `π_(-1/2)` irreducible. Put `J = (-∞, 0]`.
   - For `s ∈ J`, `s ≠ -1/2`, `π_s` is irreducible by the nonadjacent theorem
     `twoSupercuspidalNonadjacentProductIrreducible`: an isomorphism
     `ν^a ρ₀ ≅ ν^(1+b) ρ₀` forces `a = 1 + b` (`exponent_eq_of_class_eq`, from
     `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero`), which
     excludes both adjacency relations.
   - `Langlands.AllFieldBZ.glParabolicCompactScalarIntegral` gives a compact open `K` with
     `G = P K` and a Haar probability measure on `K`; `exponentHeight` and
     `exponentFamilyEquiv` realize all `π_s` on one space of smooth functions.
   - The hypotheses of the field-independent theorem `Langlands.unitarizabilityContinuation`
     hold on `J`: agreement on `K`, admissibility (`member_isAdmissible`, via
     `Langlands.AllFieldBZ.Parabolic.normalizedInductionAdmissibility`), irreducibility, a
     nonzero invariant sesquilinear form on each `π_s` (the compact pairing
     `normalizedIntegralForm_family_neg` between `π_s` and `π_(-s)` composed with the
     isomorphism `π_s ≅ π_(-s)` from the swap theorem), weak continuity in `s`, and
     unitarizability at `s = 0` (`familyZeroForm`).
   - Continuation makes `π_s` unitarizable at `s = -k/2 - 1 ∈ J`, contradicting
     `twoBlockLargeExponentNonUnitarizable`.

## Inputs over an arbitrary local field

| Input | Lean name | Module |
| --- | --- | --- |
| unitarizability continuation (field-independent) | `Langlands.unitarizabilityContinuation` | `Langlands.Representation.Unitary.UnitarizabilityContinuationProof` |
| nonadjacent irreducibility (Ze80 1.11(a)) | `Langlands.AllFieldBZ.Classification.twoSupercuspidalNonadjacentProductIrreducible` | `Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` |
| irreducible product swap | `Langlands.AllFieldBZ.Classification.irreducibleTwoFactorProductSwap` | `Langlands.AllFieldBZ.Representation.Classification.IrreducibleTwoFactorProductSwapProof` |
| large-exponent non-unitarizability | `Langlands.AllFieldBZ.Classification.twoBlockLargeExponentNonUnitarizable` | `Langlands.AllFieldBZ.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` |
| real unitarization of supercuspidals | `Langlands.AllFieldBZ.supercuspidalRealUnitarization` | `Langlands.AllFieldBZ.Representation.Unitary.SupercuspidalRealUnitarizationProof` |
| exponent family and compact pairing | `exponentHeight`, `exponentFamilyEquiv`, `normalizedIntegralForm_family_neg`, `familyZeroForm` | `Langlands.AllFieldBZ.Representation.Classification.ExponentFamily` |
| compact scalar integral | `Langlands.AllFieldBZ.glParabolicCompactScalarIntegral` | `Langlands.AllFieldBZ.Representation.Induction.CompactScalarProof` |
| twist freeness | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero` | `Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductTwistOne` |
| character twist of products | `Langlands.AllFieldBZ.Classification.twistedProductCharacterTwist` | `Langlands.AllFieldBZ.Representation.Classification.TwistedProductCharacterTwistProof` |
| binary product as two-block product | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks` | `Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalBinaryProductBridge` |

Most all-field modules in this table are ports of the corresponding p-adic modules; each port
has a Markdown page listing its declarations and its changes beyond the systematic replacement
of the field package. The nonadjacent theorem rests
on the all-field derivative theory (exactness, detection, BZ77 3.8, BZ77 4.4 and the Leibniz
filtration) and the swap theorem on the all-field Gelfand–Kazhdan theorem
`Langlands.LocalField.gelfandKazhdanContragredient`.

## Helpers in this module

The public theorems are `unitaryHalfProduct_not_isIrreducible`,
`adjacentProduct_not_isIrreducible`, `twoBlockAdjacentProduct_not_isIrreducible`, the final
theorem, and the isomorphism `determinantPowerTwistZeroIso` (`ν^0 A ≅ A`). The private
helpers are those of the p-adic module with the field package replaced: the additive
composition of real twists (`determinantPowerTwistTwistIso`, `determinantPowerTwistTripleIso`),
the exponent rigidity (`exponent_eq_of_iso`, `exponent_eq_of_class_eq`), the product functor on
blockwise isomorphisms (`twoBlockProductIso`, `twistedProductInduced_twoBlocks`), the
supercuspidal twist `scTwist`, and the facts on the members `π_s` (`member_isIrreducible`,
`member_swap`, `member_isAdmissible`, `member_equiv`, `nontrivial_of_isIrreducible`).

## Dependencies

At Library commit `2f86a99eb5616254ac5b9c399603c9bbbea15f7a`, this module and its
transitive imports comprise 1106 `Langlands` modules. A scan for the segment results of
Zelevinsky 1980 §§3, 4 and 9 found no module of the closure that is or mentions
`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
`SegmentSpecialJacquetExponentNormFormula`, `SegmentSocleProductIrreducibility`,
`MultisegmentSocleExhaustion`, `OrderedMultisegmentSocleExistence`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
`SegmentSpecialEssentialSquareIntegrability` or `SegmentSocleDerivatives`. The only
segment-named modules in the closure are `Langlands.Representation.Classification.Segments`
and its all-field port, which contain definitions and elementary transport lemmas.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On irreducible
  representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), Proposition 1.11 and the proof sketch
  of (b), printed p.175. Literature ID `zelevinsky-1980-induced-ii`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*,
  Ann. Sci. ENS (4) 10 (1977), Theorem 4.2 and Remark 4.2(2), printed p.454. Literature ID
  `bernstein-zelevinsky-1977-induced-i`.
