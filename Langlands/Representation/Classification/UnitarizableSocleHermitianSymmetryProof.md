# Hermitian symmetry of the multisegment of a unitarizable representation

`Langlands.Classification.unitarizableSocleHermitianSymmetry` proves exactly the published
proposition `UnitarizableSocleHermitianSymmetry.{uF, uV} F T`
(`TadicBlockReductionStatement.lean`). It holds for every prime `p`, `p`-adic field `F`,
topological data `T` and independent universes `uF`, `uV`, with no extra hypotheses. The
statement is Tadić 1986, §2.1–2.4. Write `π^+` for the Hermitian contragredient. A
unitarizable `π` is Hermitian (`π ≅ π^+`), and `⟨a⟩^+ = ⟨a^+⟩`. Hence `a^+ = a`, and for
a unitary cuspidal `ρ` this matches `[ν^x ρ, ν^(x+l-1) ρ]` with
`[ν^(-(x+l-1)) ρ, ν^(-x) ρ]`.

The implemented proof does not form `π^+` directly. Instead it shows that the smooth dual
`π̃` carries two labels, `ā` and `ã`. Here `ā` conjugates every segment and `ã` dualizes
every segment. The two labels must agree, and for unitary `ρ` this equality is the count
identity. The complex-conjugation results come from the helper module
`ConjugateMultisegmentSocle` (see its Markdown).

## Helper lemmas (`UnitarizableSocleHermitianSymmetryProof`)

- `isLabel_of_isZelevinskySocle`: suppose `b.IsZelevinskySocle A` on `GL_N`. Then `A` is
  irreducible (the first clause of the socle relation), and its class is a label of `b` in
  the sense of the published `Aubert.SegmentPolynomialSurjectivity.IsLabel`. The witness
  is the same datum, and `IsZelevinskySocle.isZelevinskySubrepresentation` supplies the
  subrepresentation clause.
- `eq_of_isLabel`: a label determines its multisegment. This is Zelevinsky's injectivity of
  `a ↦ ⟨a⟩`, in the rank-order form already published in
  `SegmentPolynomialSurjectivity`. Suppose `c` labels both `a` and `b`. Then
  `one_le_coeff_zeta_of_isLabel` shows that `c` occurs in `ζ(a)` and in `ζ(b)`, and
  `rankLE_of_coeff_zeta_pos` then gives `b ≤ a` and `a ≤ b` in `Multisegment.RankLE`. So
  `RankLE.antisymm` gives `a = b`. The ring inputs are the published
  `binaryProductExactness`, `gradedInductionRingLaws` and `highestDerivativeLabelStep`,
  together with some unitary additive character from
  `padicUnitaryAdditiveCharacterExists`.
- `dual_eq_conj`: for a unitary `ρ`, real `x` and `l > 0`, the dual of
  `Δ = ⟨ρ.twist x, l⟩` is the conjugate of `Δ' = ⟨ρ.twist (-(x + (l - 1))), l⟩`.
  `Segment.dual Δ` has base `dualDatum (Δ.last)`, and
  `Δ.last = ν^(l-1) ν^x ρ = ν^((l-1)+x) ρ` (`twist_twist`). By `dualDatum_twist` this base
  is `ν^(-((l-1)+x)) ρ̃`. By `conj_eq_dualDatum` (`ρ̃ = ρ̄` for unitary `ρ`) and
  `CuspidalDatum.conj_twist` it equals `(ν^(-(x+(l-1))) ρ)‾`, the base of `Δ̄'`. The
  natural-number subtraction `l - 1` is cast with `Nat.cast_sub` (using `0 < l`), and the
  exponents agree by `ring`.

## Main proof

Let `π` on `GL_N` be irreducible and unitarizable with `a.IsZelevinskySocle π`, and let
`ρ`, `x`, `l` be as in the statement.

- **`N = 0`.** The witnessing datum `d` has `d.multisegment = a`, and
  `degree_multisegment` gives `a.degree = 0`. So `a = 0` (`eq_zero_of_degree_eq_zero`), and
  both counts are `0`.
- **`N > 0`.**
  1. `π` is admissible, by the first part of the published `cuspidalEmbedding` for
     irreducible representations.
  2. Fix an invariant positive form `b`. Then `b.smoothDualEquiv` is a conjugate-linear
     equivalence `π ≃ π̃`, and `toSmoothDual_apply_action` shows it is equivariant.
  3. By the helper `Multisegment.IsZelevinskySocle.conj`,
     `(a.map Segment.conj).IsZelevinskySocle π̃`.
  4. By the published `Multisegment.IsZelevinskySocle.contragredient` (which needs
     `0 < N`), `(a.map Segment.dual).IsZelevinskySocle π̃`.
  5. The class of `π̃` therefore labels both multisegments. By `eq_of_isLabel`,
     `a.map Segment.conj = a.map Segment.dual`.
  6. `Segment.dual` is injective (it is an involution, `dual_dual`), and so is
     `Segment.conj` (`conj_injective`). `Multiset.count_map_eq_count'` then gives
     `count Δ a = count Δ.dual (a.map dual) = count Δ'.conj (a.map conj) = count Δ' a`,
     using `dual_eq_conj` in the middle step.

The statement's counts use classical decidable equality on segments (`open scoped
Classical`), and so does the theorem. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
