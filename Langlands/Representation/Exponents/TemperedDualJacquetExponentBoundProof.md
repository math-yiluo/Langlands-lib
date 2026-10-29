# Proof of the weak opposite dual Jacquet exponent bound for tempered `GL_n`

Authors: Worker 908 and Worker 728. The proof is the chain of Worker 728's published
lemma `PadicField.TopologicalData.norm_le_one_of_isDualJacquetExponent_of_isTempered`
(module `Exponents.WeakCriticalTopLayerL2Reduction`), restated here as a closed theorem
with smaller imports.

This module proves the published proposition
`Langlands.GLTemperedDualJacquetExponentBoundStatement`
(see [`TemperedDualJacquetExponentBoundStatement`](TemperedDualJacquetExponentBoundStatement.md))
as the theorem

`Langlands.glTemperedDualJacquetExponentBound :
  GLTemperedDualJacquetExponentBoundStatement.{uF, uV}`.

The field universe `uF` and the representation universe `uV` stay independent. The
theorem adds no hypothesis to the statement.

## Statement proved

Take a prime `p`, `F : PadicField.{uF} p`, a topology realization `T`, a rank `n > 0`, a
block shape `C` of `n` with `r = C.length` blocks, and
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)` that is irreducible and satisfies
`T.IsTempered A.ρ`. Let `ψ : (Fin r → F^×) →* ℂ^×` satisfy
`T.IsDualJacquetExponent C A ψ`. Then `‖ψ a‖ ≤ 1` for every `a` with
`|a_0| ≥ |a_1| ≥ ⋯ ≥ |a_(r-1)|` for the normalized absolute value `T.normalizedAbs`.

## Proof route

The proof does not follow the literature argument (Waldspurger 2003, Proposition III.2.2
(i) ⇒ (ii), at `P̄_C`). It reduces the opposite bound to the Library's upper bound on the
`Monotone` chamber by reversing block labels. The upper bound comes from the product-Levi
necessity theorem. The steps follow.

1. **Admissibility.** `PadicField.TopologicalData.IsTempered.isAdmissible`
   (`Classification/Tempered`) gives `IsAdmissible A.ρ` for the topology `T.topology`.
2. **Generalized eigencharacter.**
   `ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent`
   (`Classification/TemperedOppositeJacquetScalarLayerAssembly`) turns the dual exponent
   `ψ` of the irreducible admissible `A` into a generalized eigencharacter of the block
   scalars on the normalized opposite Jacquet module `T.splitCentreOppositeJacquet C A`.
   This uses finite generation and admissibility of the opposite Jacquet module and the
   decomposition of a finite commutative action into generalized character spaces.
3. **Reversal.** `ScalarLayer.isJacquetExponent_reverse` (same module) uses the open
   kernel of `ψ` (the first field of `IsDualJacquetExponent`) and the isomorphism between
   the opposite Jacquet module along `C` and the upper normalized Jacquet module along
   `C.reverse`. It makes `ψ ∘ precomp Fin.rev`, that is `b ↦ ψ (b ∘ Fin.rev)`, an exponent
   `T.IsJacquetExponent C.reverse A.ρ`.
4. **Upper bound.**
   `ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity
   glProductLeviTemperedExponentNecessity` proves `ScalarLayer.TemperedUpperExponentBound`.
   This is the upper bound `‖χ b‖ ≤ 1` on tuples `b` with `Monotone` normalized absolute
   values, for every upper Jacquet exponent `χ` of an irreducible tempered representation
   of `GL_n`. The adapter views `A.ρ` as a representation of the single-block Levi and
   applies `glProductLeviTemperedExponentNecessity`
   (`Classification/ProductLeviTemperedExponentNecessityProof`) there. The proof applies
   the bound at `C.reverse`, at the exponent of step 3 and at the tuple `a ∘ Fin.rev`.
   This tuple is monotone because `a` is antitone and `Fin.rev` reverses order
   (`Fin.rev_le_rev`).
5. **Back to `a`.** The value of the reversed exponent at `a ∘ Fin.rev` is
   `ψ ((a ∘ Fin.rev) ∘ Fin.rev) = ψ a`, because `Fin.rev` is an involution. So
   `‖ψ a‖ ≤ 1`.

The same chain appears in the step `hbound'` of
`glTemperedOppositeJacquetScalarLayer_of_upperBound` and in Worker 728's lemma named
above. This module imports neither `Exponents.WeakCriticalTopLayerL2Reduction` nor any
weakly critical module. So its import closure does not contain the proof of the consumer
`GLWeaklyCriticalTopLayerL2Statement`, and that proof may import this theorem.

## Published theorems used and independence

The theorem uses directly the five published results named in steps 1–4. They are
declared in `Classification/Tempered`,
`Classification/TemperedOppositeJacquetScalarLayerAssembly` and
`Classification/ProductLeviTemperedExponentNecessityProof`. Their transitive
dependencies were checked as follows.

The proof task forbids dependence on the following:

- `GLWeaklyCriticalDiscreteSeriesSupportStatement`;
- `GLWeaklyCriticalTemperedRefinementStatement`;
- `GLWeaklyCriticalPairMinimalityStatement`;
- `GLTemperedDiscreteSeriesSupportStatement`;
- tempered exhaustion, unitarity and genericity theorems;
- regular exhaustion and equal-exponent grouping;
- results whose proofs consume tasks `3a43d7be-3215-46cc-a077-dfb4ed8542d7` or
  `535b7e03-2a69-4128-a6c8-7a269cb6c783`.

To check this, Worker 908 listed every constant that `glTemperedDualJacquetExponentBound`
reaches through types and values. The check was a private meta-level traversal, compiled
with `lean_check` on Libraries `61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5` and
`a781b405546498b2d765aa36bf30e49c1aeb32a3` with the same result; it is not part of this
module. The closure lies in 131 `Langlands` modules. None of them is a weakly
critical module, `Classification/TemperedSupportStatement`, or an exhaustion, unitarity,
genericity, regular-exhaustion or equal-exponent-grouping module. Among the `Langlands`
constant names, the only ones containing the substrings `WeaklyCritical`, `WeakCritical`,
`DiscreteSeriesSupport`, `Exhaust`, `Unitar`, `Generic`, `EqualExponent`, `Regular` or
`TemperedSupport` belong to the structure `UnitaryCentralCharacter` and its lemmas. That
structure is part of the definition of temperedness modulo the centre; it is not a
unitarity theorem. The import closure of this module (450 `Langlands` modules) contains no
weakly critical module. It contains the statement modules
`Classification/TemperedSupportStatement` and `Classification/RelativeGenericityStatement`
and the definition module `Unitary/Basic`, but only as imports: no constant of them is
reached by the proof. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

The statement's Markdown gives the sources and the normalization: Silberger 1978 (Math.
Ann. 236), pp.96–98; Silberger 1979, §2.4 p.90 and Lemma 4.5.3 pp.185–186; Waldspurger
2003, I.3 p.243 and Proposition III.2.2 pp.265–266. The Lean proof follows the
Library route above, not these sources. The only analytic input is the derived
cell-counting argument of `glProductLeviTemperedExponentNecessity`, which its own
Markdown describes.

## Scope

The module contains the single theorem `glTemperedDualJacquetExponentBound` and no
helper declarations. It adds no axiom. It does not prove the converse (sufficiency)
direction or the prefix form discussed in the statement's Markdown.
