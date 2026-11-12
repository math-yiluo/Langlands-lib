# The summed Langlands head occurs in a binary product: proof

Author: Worker 186.

The theorem `Langlands.Classification.langlandsHeadProductSubquotient` proves the
unchanged published proposition
`Langlands.Classification.LanglandsHeadProductSubquotient.{uF,uV} F T` from
[LanglandsHeadProductSubquotientStatement](LanglandsHeadProductSubquotientStatement.md),
which is Tadić 1986, Proposition A.4(ii), for two positive-rank multisegments. It
adds no hypothesis. Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and the
universes `uF` and `uV` stay independent. For all `m n : ℕ` with `hm : 0 < m` and
`hn : 0 < n`, all multisegments `a b`, and all actual representations `A`, `B`, `P`
with `a.IsLanglandsHead A`, `b.IsLanglandsHead B` and `(a + b).IsLanglandsHead P`,
it proves

```
SmoothRep.IsSubquotient P ((T.binaryPositiveProductFunctor hm hn).obj (A, B)).
```

The proof uses the helper module
[LanglandsHeadDuality](../Aubert/LanglandsHeadDuality.md), which is part of this
contribution, together with published Library theorems.

## Implemented proof

Write `t` for the support-adjusted graded Aubert operator `gradedAdjustedOperator F T`
on `GradedGrothendieckGroup.{uF,uV} F T`. Write `[X]` for the class of a
finite-length representation `X`, and `coeff k c` for the multiplicity of an
irreducible class `c` in rank `k`.

1. **Ring structure.** The published proofs `binaryProductExactness F T` and
   `gradedInductionRingLaws F T hx` give the ring `gradedInductionRing F T hx hl`.
   `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T` supplies a unitary
   additive character `ψ`.
2. **Heads are irreducible.** `isIrreducible_of_isLanglandsHead` shows that `A`, `B`
   and `P` are irreducible. `degree_of_isLanglandsHead` gives `a.degree = m`,
   `b.degree = n` and `(a + b).degree = m + n`.
3. **Labels.** `exists_isLabel_of_degree` gives Zelevinsky labels `ca`, `cb`, `cab`
   of `a`, `b` and `a + b` in ranks `m`, `n` and `m + n`.
4. **Theorem P.** `gradedAdjustedOperator_label` gives
   `t (basisClass m ca) = basisClass m [A]`, `t (basisClass n cb) = basisClass n [B]`
   and `t (basisClass (m + n) cab) = basisClass (m + n) [P]`.
5. **Zelevinsky 8.4 for labels.** `one_le_coeff_label_mul` gives
   `1 ≤ coeff (m + n) cab (basisClass m ca * basisClass n cb)`.
6. **Transport by `t`.** Rewrite this inequality in the following order.
   - `coeff_gradedAdjustedOperator` with the third identity of step 4 replaces
     `coeff (m + n) cab x` by `coeff (m + n) [P] (t x)`.
   - `gradedAdjustedOperator_mul` splits `t` over the product.
   - The first two identities of step 4 turn the factors into
     `basisClass m [A] * basisClass n [B]`.
   - `basisClass_irreducibleIsoClass` writes these as classes of the actual `A` and
     `B`, and `gradedInclusion_mul_gradedInclusion` identifies their product with the
     class of the actual normalized product
     `(T.binaryNormalizedProductFunctor m n).obj (A, B)`. That product has finite
     length by `binaryProduct_preservesFiniteLength`.
   - `coeff_gradedInclusion_ofRepresentation` reads the coefficient as the
     composition multiplicity of `P` in that product.

   The result is that this multiplicity is at least one.
7. **Subquotient.** `SmoothRep.compositionMultiplicity_pos_iff_isSubquotient` turns
   positive multiplicity into
   `SmoothRep.IsSubquotient P ((T.binaryNormalizedProductFunctor m n).obj (A, B))`.
   Finally, `T.binaryNormalizedProductFunctor_of_pos hm hn` identifies the normalized
   product functor with `T.binaryPositiveProductFunctor hm hn`, which gives the
   target.

## Provenance

The target is Tadić 1986 (`tadic-1986-unitary`), Proposition A.4(ii), printed p.372
(PDF page 39). The registered source and its translation table are in the
statement's companion Markdown. Tadić proves A.4 by deformation: continuity of
characters in a twisting parameter, with his Corollary A.3 and Zelevinsky's
Proposition 8.5. This proof does not follow that route. It is the purely algebraic
alternative named in the task context. The Zelevinsky multiplicity statement
(Zelevinsky 1980, Proposition 8.4, printed p.196) is proved for labels in the
Grothendieck group. It is then transferred to Langlands heads by the Aubert
involution, which sends the Zelevinsky label of a multisegment to its Langlands head
(Theorem P in the helper module). The helper's Markdown lists its literature inputs
and the published Library theorems it uses.

This module and its helper use no unproved statement or pending task as an input.
They leave the target pair and all imported published pairs unchanged. Lean
reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
