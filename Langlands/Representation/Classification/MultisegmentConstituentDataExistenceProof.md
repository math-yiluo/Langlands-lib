# Ordered segment constituent data for every multisegment

Author: Worker 1732.

The theorem `Langlands.Classification.multisegmentConstituentDataExistence`
proves the unchanged published proposition
`Langlands.Classification.MultisegmentConstituentDataExistence.{uF,uV} F T`.
For every multisegment `a`, it constructs ordered actual segment-product data
of degree `a.degree` whose blocks are segment socles, and such data whose blocks
are segment heads. It adds no hypothesis. The module also proves the existing
proposition `MultisegmentNonprecedenceEnumeration` as
`multisegmentNonprecedenceEnumeration`.

The telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. The universes `uF` and `uV` are independent.
The multisegment and data are instantiated at `.{max uF uV, uF}`.
The resulting blocks have carrier universe `max uF uV`.

## Implemented enumeration proof

The private helper `exists_precedenceOrderedList` works with segments at an
arbitrary carrier universe. It equips them locally with the preorder

`Δ ≤ Γ ↔ ∃ k : ℕ, Γ.base = Δ.base.twist (k : ℝ)`.

Reflexivity follows from zero twisting; transitivity follows from addition of
twists. Segment lengths are ignored by this preorder, so antisymmetry is neither
asserted nor needed. If `Γ ≤ Δ` and `Δ.Precedes Γ`, precedence supplies an
integer `i > 0` taking `Δ.base` to `Γ.base`, and the reverse preorder relation
supplies an integer `j ≥ 0` taking it back. The twist-composition law would then
make `Δ.base` fixed by the integral twist `j + i`. The published theorem
`cuspidalIntegralTwistFreeness` forces `j + i = 0`, contradicting `i > 0`.

The helper uses strong induction on the multiset. For a nonempty multiset,
`Finset.exists_maximal` chooses a maximal segment `Δ` in its finite support for
this preorder. If `Δ` preceded any remaining segment `Γ`, then `Δ ≤ Γ`;
maximality would imply `Γ ≤ Δ`, contradicting the preceding argument.
Inductively enumerate `a.erase Δ`, and prepend `Δ`. The pairwise order condition
follows from the absence of such a precedence and the inductive order condition.
`Multiset.cons_erase` proves that this list has multiset `a`. Erasure removes
one occurrence, so all multiplicities are preserved, including repeated
segments with the same beginning. The empty multiset uses the empty list.

The public enumeration theorem sets `r := l.length` and `Δ := l.get`.
`List.ofFn_get` gives the ordering equality, and
`T.isPrecedenceOrdered_iff_list` converts the pairwise list condition into
`∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)`.
Applying `Multisegment.degree` to the multiset equality, together with
`List.sum_ofFn`, `List.map_ofFn` and the multiset/list coercion identities,
gives `∑ i, (Δ i).degree = a.degree`.

## Constituent data assembly

Use the enumeration theorem once. For each `i : Fin r`, the published theorem
`segmentZelevinskyConstituentExistence` supplies an actual smooth representation
`π i` with `T.IsSegmentSocle (Δ i) (π i)`. Classical choice selects this family.
The fields `r`, `Δ`, the degree equality and this family form a
`SegmentProductDatum a.degree`. Its multisegment and precedence-order conditions
are exactly those of the enumeration; its `HasSegmentSocles` condition is the
chosen family of individual socle proofs.

The second clause repeats this construction using the published
`segmentSpecialConstituentExistence`, retaining its
`T.IsSegmentHead (Δ i) (π i)` conclusion. Both individual-segment theorems are
instantiated at `.{uF, max uF uV}`; their output universe
`max uF (max uF uV)` equals `max uF uV`, as required.

The empty multisegment gives `r = 0`, degree zero, and empty block families;
the pointwise constituent conditions are vacuous. No representation of the full
multisegment product is constructed by this theorem. The socle and head
conditions here concern the individual segment blocks and retain the strong
image/kernel uniqueness built into `IsSegmentSocle` and `IsSegmentHead`.

## Sources and dependencies

This is a derived combination of Zelevinsky's individual-segment constituents
and multisegment ordering: A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), 165–210, §§3.1 (printed pp.180–181, PDF pp.17–18),
6.5 (printed p.189, PDF p.26), and 9.1 (printed p.197, PDF p.34).
The registered original is `zelevinsky-1980-induced-ii`, PDF SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The target's paired Markdown records this derived provenance. The finite
maximal-element argument above is the implemented internal proof of the ordering;
it does not require choosing unitary exponents or a global linear order.

The project imports are the unchanged target statement module and the published
proof modules `CuspidalIntegralTwistFreenessProof`,
`SegmentZelevinskyConstituentExistenceProof` and
`SegmentSpecialConstituentExistenceProof`. The remaining direct imports provide
Mathlib's finite-preorder maximal-element theorem and finite-sum bookkeeping.
The constituent existence and twist-freeness inputs are proved declarations,
not assumptions of their proposition definitions. This module needs no
multisegment constituent-existence or classification theorem as a proof input.
