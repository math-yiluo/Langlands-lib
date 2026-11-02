# Renard B.III: the unital separation lemma

`Langlands.Renard.unitalSeparation` proves the unchanged published
`Langlands.Renard.UnitalSeparationStatement` from
`Langlands.Algebra.SeparationStatements`:

```lean
theorem unitalSeparation (A : Type u) [Ring A] [Algebra ℂ A] :
    UnitalSeparationStatement A
```

For every unital complex algebra `A` in an arbitrary universe `u`, if
`Module.rank ℂ A ≤ Cardinal.aleph0`, then every nonnilpotent `a : A` has
an actual maximal left ideal `I : Submodule A A` such that
`IsSimpleModule A (A ⧸ I)` and `a • I.mkQ 1 ≠ 0`. The theorem adds no
nontriviality, commutativity, topology or finite-dimensionality premise.
The countability assumption is on vector-space rank, and is used only to
obtain the scalar shift.

The proof applies the published theorem
`Langlands.Renard.nonnilpotentLeftResolvent` from
`Langlands.Algebra.NonnilpotentLeftResolventProof` to the rank bound and
nonnilpotence hypothesis. This gives a nonzero `z : ℂ` for which
`a - algebraMap ℂ A z` has no left inverse. It then applies
`Langlands.Renard.leftShiftSimpleQuotient`, obtaining a coatom `I`, the
principal-left-ideal containment, simplicity of the actual quotient module,
and nonzero action on the class of `1`. Dropping the containment conjunct
produces exactly `UnitalSeparationStatement A`. The resolvent argument is
reused by its published Lean name; it is not assumed or reproved here.

The quotient step applies `principalLeftIdealProper` to the shift and
`Ideal.exists_le_maximal` to its proper principal left ideal. The coatom
property makes the quotient simple. If `a ∈ I`, subtracting the shift
places `algebraMap ℂ A z` in `I`; multiplying on the left by the inverse
scalar places `1` in `I`, contradicting properness. Thus `a ∉ I`, which
means `a • I.mkQ 1 = I.mkQ a ≠ 0`. These are left ideals and quotient left
modules throughout. The quotient also carries the complex structure and
scalar tower inherited from the algebra, as checked in the statement
module. No quotient ring is used.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, B.III, Lemme and proof,
printed page 273 / one-based PDF page 279. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The source first adjoins a unit and then obtains the nonzero shift from
B.I and its proof. After constructing the nonzero cyclic quotient, it
uses A.VI.3, Proposition (i), printed page 264 / PDF270, to take a simple
quotient. Here the maximal-left-ideal theorem provides the inverse-image
ideal directly, with the same contradiction using the nonzero scalar.
The conclusion retains the explicit separating vector shown by that
argument: the class of `1`.

Worker 1210 read the entire B.III page as extracted text and rendered image,
A.VI.3 PDF269–270 as text, and the supplementary older-edition errata
PDF18–19. Both source hashes were verified. The registered older errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF19,
remove the old right-zero-divisor assertion and preserve the absence of a
left inverse, as already incorporated in the 2026 text. No separate
Renard errata note was present in the current Library.

This theorem covers the unital case reached after the source's
unitization step. The original nonunital-action reduction, including
preservation of rank, nonnilpotence, action and simplicity, remains a
separate parent obligation. It is not a premise of this unital theorem.
The zero algebra is included: its nonnilpotence premise is never true.

Worker 1210 wrote this composition and the principal-left-ideal and
simple-quotient proofs on which it depends. Worker 972 authored the
published one-sided resolvent theorem. Worker 221 and Worker 6 authored
the published separation statements and their informal source-route
outline. Reusing the published theorem does not alter its proof module.

Development check `5562a771-d597-4be5-adf4-f4a464a2e480` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the entry module with zero
errors and warnings. Inspection reports the sole universe parameter `u`
and the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Independent semantic acceptance and publication remain separate gates.
