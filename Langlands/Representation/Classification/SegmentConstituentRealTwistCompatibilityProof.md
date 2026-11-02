# Real determinant twists of all four segment constituent relations

Authors: Worker 34; Worker 699 (complete-type and strong-uniqueness checks).

The theorem
`Langlands.Classification.segmentConstituentRealTwistCompatibility`
proves exactly the published proposition
`Langlands.Classification.SegmentConstituentRealTwistCompatibility.{uF,uV} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime]`,
`(F : PadicField.{uF} p)` and `(T : F.TopologicalData)`.
The field universe `uF` and supercuspidal-carrier universe `uV` are
independent. Actual candidates and induced representations have carriers in
`max uF uV`.

For every segment `Δ`, real number `s` and actual smooth complex
representation `π` of `GL_(Δ.degree)(F)`, the theorem preserves and reflects
the strong socle, strong head, irreducible subrepresentation and irreducible
quotient relations under the common determinant twist `|det|^s`. The segment
on the other side is `Δ.twist s` and the candidate is the prescribed smooth
twist of `π`.

This is an internal proof of the derived real-twist target. Its provenance
is the twist derivation in
[SegmentConstituentCompatibilityStatement.md](SegmentConstituentCompatibilityStatement.md),
implemented using the published actual induction and algebraic transport
constructions. No additional assertion from the original literature is used.
The published target and all its imported Lean/Markdown pairs are unchanged.

## Actual induction comparison

The helper
`Langlands.PadicField.TopologicalData.segmentInducedRealTwistEquiv`
is defined for every actual smooth representation `A` of `GL_r(F)`, every
natural length `m`, a proof `0 < r`, and real `s`. It supplies an actual
equivariant linear equivalence

```text
twist |det_(mr)|^s (segmentInduced A m)
    ≃ segmentInduced (segmentFactor A s) m.
```

It does not require irreducibility, supercuspidality or positive `m`.
The main theorem applies it with the positive length of its segment.

The proof forms the smooth character `|·|^s` on the field's units using
`isOpen_ker_realPowerCharacter` and the published openness of the normalized
absolute-value kernel. Composing this unit character with the determinant
is definitionally the prescribed `T.determinantPowerCharacter`.
`T.normalizedProductDeterminantTwistEquiv` then moves the common twist onto
the actual block factors of the uniform block shape with `m` blocks of
size `r`.

For block index `i`, the resulting action is
`twist |det_r|^s (twist |det_r|^i A.representation)`.
Two applications of `twist_twist` and commutativity of the two complex
characters identify it with
`twist |det_r|^i (twist |det_r|^s A.representation)`.
This is the `i`th factor of the increasing product for the twisted `A`.
The proof turns each action equality into an actual equivalence using
`equivOfRepresentationEq`, then applies
`T.normalizedProductInducedEquiv` to the family of these equivalences.
Composing with the common determinant-twist equivalence gives the helper.
This use of actual block equivalences retains the dependent carriers of
both induced spaces.

The normalized upper parabolic, positive half-modulus covariance and right
translation are those of the imported induction constructions throughout.
The common-twist map in the first comparison multiplies an induced function
at `g` by `|det g|^s`; the second comparison is induction of the identity
linear equivalence on each block action.

## Four relations and strong uniqueness

The closing proof chooses one actual supercuspidal representative `A` of
`Δ.base.cls` using `Quotient.exists_rep`. The published
`GeneralLinear.SupercuspidalRep.twist` supplies its actual supercuspidal
twist `As`. The class of `As` is the beginning of `Δ.twist s`, by the
definition of the class twist and the chosen class equality.

For each relation, the corresponding `isSegment*_iff` from `Segments`
expresses the relation using these fixed representatives. The proof
composes the reverse of the corresponding algebraic
`isIrreducible*_twist_iff` with `isIrreducible*_iff_of_equiv` for the actual
induction equivalence. This gives both directions for each of the four
relations, in the exact conjunction order of the target.

The strong relations retain their full image and kernel uniqueness clauses.
Transport along the actual ambient equivalence pulls an arbitrary
irreducible embedding back with its inverse and pushes equality of its range
forward; for heads it composes an arbitrary quotient map with the ambient
equivalence and transports equality of kernels. Common twisting keeps every
underlying linear map unchanged, so the published twist biconditionals
preserve and reflect these same subspaces. All competitors range over the
full algebraic carrier universe `max uF uV`; no smoothness restriction on
competitors is introduced.

## Dependencies and scope

The direct imports are the published target,
`Classification.ConstituentCompatibilityAlgebraicProof`,
`Induction.NormalizedProductCharacterTwist` and
`Induction.BlockEquivalence`. The proof uses actual representatives,
intertwiners and induction equivalences. It has no additional
theorem-valued assumptions and does not use segment classification,
multisegment or quotient exhaustion, ordered-head existence, tempered-block
uniqueness, square-integrable classification or regular exhaustion.
It asserts compatibility of the relations; it supplies no constituent
existence theorem.

The development check compiles the paired module in the prepared Lean
4.34.0 environment and inspects the closing theorem's universe parameters
and axioms. Its only axioms are `propext`, `Classical.choice` and
`Quot.sound`. Independent semantic review, exact-target machine validation
and Library publication remain separate requirements.
