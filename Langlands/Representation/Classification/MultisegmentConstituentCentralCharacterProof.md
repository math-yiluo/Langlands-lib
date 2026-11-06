# The scalar action on multisegment socles and Langlands heads

Authors: Worker 1715 (original proof and explanation) and Worker 1737
(verification, documentation refinement, and submission).

The closing theorem
`Langlands.Classification.multisegmentConstituentCentralCharacter F T`
proves exactly the published proposition
`Langlands.Classification.MultisegmentConstituentCentralCharacter.{uF, uV} F T`
from [MultisegmentConstituentCompatibilityStatement](MultisegmentConstituentCompatibilityStatement.md).
The field universe `uF` and the supercuspidal carrier universe `uV` are
independent and arbitrary. The proof covers every prime `p`, every
`F : PadicField.{uF} p` and every `T : F.TopologicalData`. The statement pair
and the pairs it imports are unchanged.

Fix segments `Δ_1, …, Δ_r`, supercuspidal representatives `A_i` of the bases
`Δ_i.base`, and characters `ω_i` such that `z · 1` acts on `A_i` by `ω_i(z)`.
Let `a` be the multiset `{Δ_1, …, Δ_r}`. The theorem shows that every `π`
satisfying `a.IsZelevinskySocle π` or `a.IsLanglandsHead π` has scalar
character `∏ i, (ω_i^(length Δ_i) · (ν_(degree Δ_i)^((length Δ_i - 1)/2) ∘ scalar))`.
Here `ν_k^s` is `T.determinantPowerCharacter k s`, so each segment factor
evaluates at `z : Fˣ` as
`ω_i(z)^(length Δ_i) |z|_F^((rank Δ_i)(length Δ_i)(length Δ_i - 1)/2)`.

The proof is an internal reduction to the published segment formula
`Classification.segmentConstituentCentralCharacter` and to the published
scalar-character lemma for normalized product induction. It adds no hypotheses.
It uses no classification, independence of the ordering, square-integrability
or irreducibility of the induced representation. Nor does it use precedence
ordering or the uniqueness clauses of the head and socle relations. The source
provenance of the formula is that of the published statement, whose Markdown
explains why the formula is derived. This module adds no claim from the original
literature.

## Declarations

`HasScalarCharacter ρ z ω` is the published predicate
`∀ c v, ρ (z c) v = (ω c : ℂ) • v` from `Classification.ConstituentRelations`.
All declarations are in the namespace `Langlands.Classification`.

| Declaration | Content |
| --- | --- |
| `exists_equiv_of_ofFn_eq f g h` | For `f : Fin r → α` and `g : Fin s → α`, if `List.ofFn f` and `List.ofFn g` have the same multiset, then there is `e : Fin r ≃ Fin s` with `f i = g (e i)` for all `i`. |
| `hasScalarCharacter_of_segmentHead_or_socle F T` | Let `π` be a representation of `GL_(deg Δ')(F)` on a carrier in `max uF uV` with `T.IsSegmentHead Δ' π` or `T.IsSegmentSocle Δ' π`. Suppose `Δ' = Δ` and `A` represents `Δ.base` with scalar character `ω`. Then `π` has scalar character `ω^(length Δ) · ν_(deg Δ)^((length Δ - 1)/2) ∘ scalar`. |
| `multisegmentConstituentCentralCharacter F T` | The exact target. |

## Implemented proof

**Reindexing.** `exists_equiv_of_ofFn_eq` turns the multiset equality into a
list permutation by `Quotient.exact`. Batteries' `List.Perm.idxBij` then gives
an index bijection whose inverse is the bijection of the reversed permutation.
`List.Perm.getElem_idxBij_eq_getElem` gives the value identity, and conjugating
by `finCongr List.length_ofFn` gives the claimed `Fin r ≃ Fin s`. The argument
is the same as the private `ofFn_matching` in
`Classification.TemperedBlockUniquenessReduction`; that private helper is
not exposed for reuse by name.

**One segment constituent.** In `hasScalarCharacter_of_segmentHead_or_socle`,
substituting `Δ' = Δ` lets the representation of `GL_(deg Δ')(F)` be used for
`Δ`. The published `IsSegmentHead.isSegmentQuotient` and
`IsSegmentSocle.isSegmentSubrepresentation` weaken the head or socle relation
to a quotient or subrepresentation relation. The third conjunct of the
published `segmentConstituentCentralCharacter F T Δ ω A hA hω` then gives the
scalar character.

**The multisegment constituents.** Unfolding `Multisegment.IsZelevinskySocle`
or `Multisegment.IsLanglandsHead` gives a segment product datum `d` with
`d.multisegment = a`. For the socle, every block `d.blocks j` is a segment socle
of `d.segments j`, and there is an injective intertwiner from `π` into
`d.induced`. For the head, every block is a segment head, and there is a
surjective intertwiner from `d.induced` onto `π`. Since `d.multisegment` is by
definition the multiset of `List.ofFn d.segments`, `exists_equiv_of_ofFn_eq`
gives `e : Fin d.length ≃ Fin r` with `d.segments j = Δ_(e j)`. By the
single-segment lemma, with the representative `A_(e j)` and its character
`ω_(e j)`, block `j` has the scalar character `ω_Δ(e j)` of the segment
`Δ_(e j)`. The published `T.hasScalarCharacter_normalizedProductInduced`, for
the block shape `d.shape` with sizes `deg (d.segments j)`, shows that
`d.induced` has scalar character `∏ j, ω_Δ(e j)`. `Equiv.prod_comp e` rewrites
this product as `∏ i, ω_Δ(i)`. Finally the published
`HasScalarCharacter.of_injective` (socle case) or
`HasScalarCharacter.of_surjective` (head case) transports the character to
`π`. Both carriers lie in `max uF uV`, as these lemmas require.
