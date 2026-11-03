# Full centralizer compatibility on a maximal split torus

`Langlands.BruhatTits.Cartan.centralizerSplitCompatibility` proves
exactly the published proposition
`Langlands.BruhatTits.Cartan.CentralizerSplitCompatibilityStatement.{u}`.
It imports the statement and its existing normalization laws without changing
any of their Lean or Markdown files.

## Sources and provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, Axiom 4.1.4(A1) and Remark
4.1.5, printed page 159 / PDF page 190, specify the negative apartment
translation associated with the centralizer valuation. Definition 6.1.2(V6),
printed page 199 / PDF page 230, states full centralizer compatibility and
its consequence for split-torus points. The source file is
`Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023.pdf` in the
registered publication folder; its SHA-256 is
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF page 25, correct the character
valuation to the positive field order. Their Chapter 4 and Chapter 6
corrections, PDF pages 27–29 and 32, leave the two axioms used here
unchanged. The extra Chapter 7 AS5 hypothesis on PDF page 33 remains a
separate building obligation. The corrections file is
`Kaletha-Prasad--Corrections and additions to Bruhat-Tits theory, a new approach--2024.pdf`;
its SHA-256 is
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Both files are retained under the Central-Library publication folder
`Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

This proof is an internal restriction argument implementing the displayed
consequence of V6 with the Library's actual rational-point maps and normalized
valuation. Worker 1501 adapted the general identity-comparison argument of the
unreviewed `CentralizerSplitCompatibility` draft by Workers 1266 and 1238,
revision 2 of task `2c10c842-7214-42a0-9b8d-288c6470a063`. Both draft authors
are coauthors of this contribution. The evaluation helper is private to this
module and differs from the private helper of the published coordinate proof
`Langlands.BruhatTits.Cartan.coordinateCentralizerSplitCompatibility`, so the
two sibling proofs share no unpublished helper.

## Exact hypotheses

The theorem has the unchanged type of the published proposition. The field
`F : Type u` has `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances, covering both equal and mixed
characteristic. The ambient group scheme `G` is affine and connected
reductive. The torus `S` is an arbitrary commutative group scheme over `F`
whose inclusion `i : S.toGrp ⟶ G` satisfies `IsMaximalSplitTorus i`; no
coordinate model of `S` is chosen, and the ambient group need not be split or
quasi-split.

The argument uses the given `C : CentralizerDatum i`: its actual group `C.Z`,
representing inclusion `C.j`, factorization `C.s`, identity `C.s ≫ C.j = i`
and comparison bijectivity `C.bijective`. The latter is supplied by the
datum, not proved here. The explicit premise

```text
Function.Bijective (restrictionEvaluation (𝟙 S.toGrp))
```

is retained and used; this theorem does not establish it.

For every `RootFunctionFamily` on `S`, the premise is the full
`IsCentralizerCompatible i C.j C.s C.bijective φ`. The conclusion is exactly
`IsSplitTorusCompatible i (localFieldOrder F) φ`. There is no finiteness
premise on values of the family. The separate root-datum valuation axioms
are not needed for this implication between compatibility predicates.

## Implemented proof

The private helper `eval_torusValuationRestriction_of_id` first rewrites
`torusValuationRestriction C.s C.bijective` by the published
`torusValuationRestriction_eq_id`, using the identity-comparison premise, to
the positive valuation `centralizerValuation (𝟙 S.toGrp)` of the torus
itself. The published `centralizerValuation_spec` for the identity evaluates
this valuation at the restriction of a rational character `χ` as the real
cast of `rationalCharacterValuation`. Taking `χ` to be the rational character
corresponding to a lattice character `a`, `characterRestrict_id` reduces
`characterRestriction (𝟙 S.toGrp) χ` back to `a`, and unfolding
`localFieldOrder` and `rationalCharacterValuation_apply` identifies the right
side with the real cast of the normalized integer field order of `a(t)`.
Hence

```text
eval S a (torusValuationRestriction C.s C.bijective t) = ord(a(t)),
```

where `ord` is `localFieldOrder F`.

For an actual relative root `a`, torus point `t` and root-group point `u`,
the proof applies full V6 to `rationalPoints.map C.s t`. Associativity of
scheme morphism composition and `C.comp_eq` give

```text
rationalPoints.map C.j (rationalPoints.map C.s t) = rationalPoints.map i t.
```

Since `torusValuationRestriction` is the composite of the centralizer
valuation with `rationalPoints.map C.s`, the helper supplies the positive
valuation evaluation at this point.
`centralizerTranslation_toAdd` changes translation to the negative of that
valuation, and `map_neg` moves the negative sign through the linear character
evaluation. Substitution in full V6 yields

```text
φ_a(i(t)⁻¹ u i(t)) = φ_a(u) + (-ord(a(t))).
```

Both sides remain in `WithTop ℝ` throughout; the proof uses no cancellation
or finite-value reduction. The connected-reductive, maximality and represented
centralizer hypotheses are retained by the exact target, although the
calculation itself only needs the supplied full V6, factorization and the two
comparison bijectivity premises.

## Scope

This theorem proves the general identity-comparison compatibility
implication. It constructs no centralizer and proves no automatic
character-comparison bijectivity, root-datum valuation, corrected building or
corrected-building existence. It supplies neither V7 nor AS5. Actual
`Z(F)^0`, `G(F)^0`, parahorics, compactness and Cartan coverage remain
separate obligations. The coordinate target without the identity premise is
proved separately by `coordinateCentralizerSplitCompatibility`.
