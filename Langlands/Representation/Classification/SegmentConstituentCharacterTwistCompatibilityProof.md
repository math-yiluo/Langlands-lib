# Character twists of all four segment constituent relations

Authors: Worker 1715 and Worker 1597. Worker 1715 supplied the complete
initial proof draft; Worker 1597 checked it against the current Library and
prepared this focused submission.

The theorem
`Langlands.Classification.segmentConstituentCharacterTwistCompatibility`
proves exactly the published proposition
`Langlands.Classification.SegmentConstituentCharacterTwistCompatibility.{uF,uV} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime]`,
`(F : PadicField.{uF} p)` and `(T : F.TopologicalData)`.
The field universe `uF` and supercuspidal-carrier universe `uV` are
independent. Candidates and induced representations have carriers in
`max uF uV`.

Fix a segment `Δ`, a character `χ : F^× → ℂ^×`, proofs that `χ ∘ det` has
open kernel on `GL_(Δ.rank)(F)` and on `GL_(Δ.degree)(F)`, and a smooth
complex representation `π` of `GL_(Δ.degree)(F)`. The theorem shows that
twisting by `χ ∘ det` preserves and reflects four relations: the strong
socle, the strong head, the irreducible subrepresentation and the irreducible
quotient. The segment on the other side is the target's `Δχ`: its base class
is the published `SupercuspidalClass.twist` of `Δ.base.cls` by `χ ∘ det`, and
its length is unchanged. The candidate on the other side is the target's
smooth twist `πχ` of `π`.

This is an internal proof of the target, which is BZ77 Proposition 1.9(f)
together with Ze80 §§3.1 and 9.1 (see
[SegmentConstituentCompatibilityStatement.md](SegmentConstituentCompatibilityStatement.md)).
The proof follows the published proof of the real-twist case
(`SegmentConstituentRealTwistCompatibilityProof`) and uses only published
induction and algebraic transport constructions. It uses no other assertion
from the literature. The target and all its imported Lean/Markdown pairs are
unchanged.

## Openness of the kernel on `F^×`

The published `T.normalizedProductDeterminantTwistEquiv` needs a smooth
character of `F^×`, which is an open-kernel character of the field's units.
The target gives openness only after composing with the determinant, so the
module proves two helper results in `Langlands.PadicField.TopologicalData`.

* `determinant_diagonalUnits_mulSingle`: for `j : Fin r` and `a : F^×`, the
  diagonal unit matrix with `a` at `j` and `1` elsewhere has determinant `a`.
  The proof uses `Matrix.det_diagonal` and `Finset.prod_eq_single`.
* `isOpen_ker_of_isOpen_ker_comp_determinant`: if `0 < r` and `χ ∘ det` has
  open kernel on `GL_r(F)`, then `χ` has open kernel on `F^×`. The map
  `s(a) = diag(a, 1, …, 1)` is continuous by the published
  `continuous_diagonalUnits` composed with `continuous_mulSingle`. By the
  previous lemma, `ker χ = s⁻¹(ker (χ ∘ det))`, and the preimage of an open
  set is open.

The main proof applies the second lemma with `r = Δ.rank`, which is positive
by `Δ.rank_pos`, and bundles `χ` as a smooth character `χs`.

## Induction comparison

The helper
`Langlands.PadicField.TopologicalData.segmentInducedCharacterTwistEquiv`
takes:

* a smooth representation `A` of `GL_r(F)`, a natural length `m` and a proof
  of `0 < r`;
* a smooth character `χ` of `F^×`;
* a proof that `χ ∘ det` has open kernel on `GL_r(F)`.

It returns an equivariant linear equivalence

```text
twist (χ ∘ det) (segmentInduced A m)  ≃  segmentInduced (A.twist (χ ∘ det)) m.
```

It does not require irreducibility, supercuspidality or positive `m`.

The first step applies `T.normalizedProductDeterminantTwistEquiv` on the
uniform block shape with `m` blocks of size `r`. This moves the common twist
onto the block factors. The `i`th block action becomes
`twist (χ ∘ det) (twist |det_r|^i A.representation)`. Two applications of
`twist_twist` and commutativity of the two characters (`mul_comm`) rewrite
it as `twist |det_r|^i (twist (χ ∘ det) A.representation)`, the `i`th factor
of the increasing product for the twisted `A`. Each action equality becomes
an equivalence via `equivOfRepresentationEq`, and
`T.normalizedProductInducedEquiv` induces the family. Composing the two
equivalences gives the helper. Both induced spaces keep their dependent
carriers.

## Four relations

The main proof chooses a supercuspidal representative `A` of `Δ.base.cls` by
`Quotient.exists_rep`. Its twist `Aχ` is the published
`GeneralLinear.SupercuspidalRep.twist` of `A` by `χ ∘ det`, using the given
open kernel on `GL_(Δ.rank)(F)` and `ker_determinant_le_ker_comp χ`. By the
definition of the class twist and the chosen equality of classes, the class
of `Aχ` is the base of `Δχ`. Applying the helper to `A.obj`, `Δ.length`,
`Δ.rank_pos` and `χs` gives the ambient equivalence `e`.

Each relation is handled the same way. The corresponding `isSegment*_iff`
from `Segments` restates it for `(Δ, π, A)` and for `(Δχ, πχ, Aχ)`. Then the
reverse of the algebraic `isIrreducible*_twist_iff` from
`ConstituentCompatibilityAlgebraicProof` is composed with
`isIrreducible*_iff_of_equiv e`. This gives both directions of each of the
four biconditionals, in the target's conjunction order. As in the real-twist
case, the strong relations keep their full uniqueness clauses, because
twisting leaves every underlying linear map unchanged.

## Dependencies and scope

The direct imports are:

* the target module `Classification.SegmentConstituentCompatibilityStatement`;
* `Classification.ConstituentCompatibilityAlgebraicProof`;
* `Induction.NormalizedProductCharacterTwist`;
* `Induction.BlockEquivalence`;
* `Group.GL.UpperBruhatCells`, for `continuous_diagonalUnits`.

The proof has no theorem-valued assumptions. It asserts compatibility of the
relations and supplies no constituent existence theorem.

The development check compiles the module in the prepared Lean 4.34.0
environment with no errors or warnings. The closing theorem's only axioms are
`propext`, `Classical.choice` and `Quot.sound`. Independent semantic review,
exact-target machine validation and Library publication are still required.
