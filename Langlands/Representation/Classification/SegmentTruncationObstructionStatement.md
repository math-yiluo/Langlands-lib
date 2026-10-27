# The finite segment-truncation obstruction

Author: Worker 684.

`Langlands.Classification.SegmentTruncationObstruction.{uF,uV} F T` states
the combinatorial lemma at the end of Zelevinsky 1980 §9.8, printed
pp.199–200. This contribution defines a proposition; the obstruction remains
unproved here. It proves neither the special-head irreducibility criterion
nor any representation classification result.

The outer parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, and `T : F.TopologicalData`. The field universe `uF`
and supercuspidal carrier universe `uV` are independent. Every segment is the
published actual `T.Segment.{uV,uF}`; the carrier universe is `uV`, without
replacing it by `max uF uV`.

For every natural number `r`, take a family `Δ : Fin r → T.Segment` and two
families `A B : Fin r → Option T.Segment`. The three transparent helpers in
`Langlands.PadicField.TopologicalData.Segment` mean:

- `optionalSupport none = ∅` and `optionalSupport (some E) = E.support`.
- `IsTerminalTruncation (A i) (Δ i)` holds automatically for `none`. For
  `some E`, it says `E.support ⊆ (Δ i).support` and
  `(Δ i).last ∈ E.support`.
- `IsInitialTruncation (B i) (Δ i)` also holds for `none`. For `some E`,
  it says `E.support ⊆ (Δ i).support` and `(Δ i).base ∈ E.support`.

Thus an empty truncation is represented by `none`, and every nonempty
truncation is an actual segment, rather than an arbitrary subset or a
substitute interval structure. Truncating at the beginning retains the
terminal endpoint for `A`; truncating at the end retains the initial endpoint
for `B`. The definitions permit the whole original segment.

Write `U_A = ⋃ i, optionalSupport (A i)` and
`U_B = ⋃ i, optionalSupport (B i)`. If the truncation conditions hold,
`U_B = (fun ρ => ρ.twist 1) '' U_A`, and `U_B.Nonempty`, the proposition
asserts `∃ i j : Fin r, (Δ i).IsLinked (Δ j)`. Here `CuspidalDatum.twist 1`
is the actual residue-normalized determinant twist `νρ`. An image under this
function is precisely the union of the shifted terminal supports. The
nonemptiness is imposed on the common shifted union as in the source; the
image equation also implies `U_A` is nonempty.

The union is an ordinary set union; it does not count multiplicities. The
indexed family retains repetitions, with no injectivity or distinctness
premise. This agrees with the arbitrary list of segments in the lemma.
The conclusion needs no explicit inequality: the published
`Segment.not_isLinked_self` excludes equal segment values, and hence equal
indices, for any linked witnesses. The case `r = 0` is included. Its unions
are empty, so its nonemptiness hypothesis cannot hold. The same applies if
all truncations are empty.

## Source correspondence and proof boundary

The original was read in text and rendered form, including the complete
combinatorial proof and figure on printed p.200:

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980), registered as
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- Retained original:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
  Locator: §9.8, truncation definitions and lemma on printed p.199,
  conclusion and entire proof on printed p.200 (resource PDF pages 36–37).

The source's `Δ_i'` are `A i`, and its `Δ_i''` are `B i`. Its terminal
condition retains the end of `Δ_i`; its initial condition retains the
beginning. The source equation is
`⋃ Δ_i'' = ⋃ (ν Δ_i') ≠ ∅`, exactly the shifted union and nonemptiness above.
`IsLinked` already means that neither original support contains the other
and their union is a segment support, following Zelevinsky §4.1.
No matching source errata entry was found in the available project notes or
literature index.

The source proof supposes all original segments are unlinked, chooses
`ρ ∈ U_A` with `νρ ∉ U_A`, and selects a terminal truncation containing `ρ`.
Then `ρ` is the end of that truncation and its original segment `Δ_i`.
The equation places `νρ` in an initial truncation of `Δ_j`. Nonlinkage
forces `Δ_i ⊆ Δ_j`. If `ρ₁` is the beginning of `Δ_j`, initial truncation
and the equation put `ν⁻¹ρ₁` in a terminal truncation of `Δ_k`.
Nonlinkage now forces `Δ_j ⊆ Δ_k`. The terminal truncation of `Δ_k`
therefore contains `νρ`, contradicting the choice of `ρ`.

This paragraph records the source argument, not an implemented Lean proof.
A successor must justify the finite-union endpoint choice using independently
proved integral twist freeness for actual cuspidal classes; finiteness alone
would not justify it on an arbitrary periodic orbit. It must derive both
support-containment steps from actual nonlinkage, handling contained segments
and different twist lines, and prove any integer or rational coordinate bridges.
No freeness hypothesis, classification hypothesis, or endpoint-choice axiom
is added to the proposition.

The helper definitions are internal notation for exactly the empty-or-segment
alternatives and endpoint membership in the source. The only project import is
`Classification.Segments`, supplying actual segments, cuspidal twists and
support-based linkage. No proof of freeness or higher classification is imported.
