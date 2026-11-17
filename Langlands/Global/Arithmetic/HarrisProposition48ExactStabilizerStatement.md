# Harris's Proposition 4.8 under the exact Weil stabilizer condition

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerStatement`,
namespace `Langlands.Global.Harris`.

## The statement

`Proposition48ExactStabilizerStatement.{uF, uE, uE', uL, uV} : Prop` restates
Harris 1998, Proposition 4.8 (printed p.201) with the auxiliary character
subject to Harris's condition (4.12) (proof of Lemma 4.7, printed p.204).
For every prime `p`, `p`-adic field `F`, finite extension `F'/F`, CM number
fields `E ⊆ E'` with `L` (number field with the algebra maps of the published
statement), `CompactSpace (AdeleQuotient E)`, reciprocity family `e`,
characters `χ χs` of `F'^×`, subfield `K₀ ⊆ E`, place data `P Ps` and Hecke
character `ξ` of `E'`: if `NormalizedReciprocity F e` and
`IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ`, then there are `r : ℕ`
and `c : CuspidalOperatorRealization.IsoClass E r` such that

- `c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ`,
- `c.IsRegularAlgebraic`,
- `c.IsConjugateSelfDual`,
- `c.HasSupercuspidalComponent.{uE, uV} Ps.v`.

Here `CuspidalOperatorRealization.IsoClass E r` is the type of irreducible
cuspidal classes of `GL_{r+1}(𝔸_E)`: the published realizations have matrix
size `r + 1` (`CuspidalOperatorRealization.lean`, lines 26–27), so the index
`r` is the rank minus one. The first conclusion fixes the rank: the published
theorem
`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.rank_eq`
gives `r + 1 = Module.finrank E E' = [E' : E]`, which is Harris's `n`. This
is the same rank convention as the published `Proposition48Statement`.

## The single change

It is literally the published `Proposition48Statement`
(`HarrisProposition48Statement.lean`, line 43), with the same binders in the
same order, the same instance arguments, the same universe parameters
`uF uE uE' uL uV` and the same four-part conclusion, except that the premise

```
IsProposition48Datum e χ χs K₀ P Ps ξ
```

is replaced by

```
IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ
```

The new datum (module `HarrisProposition48ExactStabilizerData`) is
`IsProposition48Datum` with its one conjunct
`IsInGeneralPosition F F' (weilCharacter F e F' χs)` replaced by
`GeneralPosition.HasExactWeilStabilizer F F' (weilCharacter F e F' χs)`.
A private audit (not submitted) checked mechanically that the value of
`Proposition48ExactStabilizerStatement` is the value of
`Proposition48Statement` with the constant `IsProposition48Datum` (which occurs
once) replaced by `IsProposition48ExactStabilizerDatum`, with the same
universe parameters.

## Relation to the published statement

The theorem
`proposition48ExactStabilizerStatement_of_proposition48Statement` proves

```
Proposition48Statement.{uF, uE, uE', uL, uV} →
  Proposition48ExactStabilizerStatement.{uF, uE, uE', uL, uV}
```

by applying the given statement to the same data and passing from the
exact-stabilizer datum to the general-position datum with
`IsProposition48ExactStabilizerDatum.isProposition48Datum`, which uses the
published theorem `Langlands.Global.generalPositionOfExactStabilizer`
((4.12) ⇒ general position). It uses only the standard axioms.

## What is not claimed

`Proposition48ExactStabilizerStatement` is not proved here. It is a weaker
proposition than `Proposition48Statement`: its hypothesis is stronger, and
`Proposition48Statement` implies it by the theorem above. Its consumers must
supply auxiliary characters with the exact stabilizer. Neither inheritance
statement of the sibling module
`HarrisProposition48ExactStabilizerInheritanceStatement` is proved here or
there. The published `Proposition48Statement`, its datum and its open tasks
are unchanged and stay as the fallback.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8: printed p.201 (PDF p.25); setup of Section 4: pp.200–201;
  proof of the proposition: pp.201–203. Condition (4.12): proof of Lemma 4.7,
  printed p.204 (PDF p.28), the proof running over pp.204–206: with
  `G = Γ_F`, `H = Γ_{F'}` and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`,
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}`.
- Design: operator plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8: Remark 4.2 (`rem:noDrinfeld`, TeX lines 859–894), and the
  recommendation to restate Prop. 4.8 with the stabilizer condition in place
  of general position, in the datum and in the validity predicates (item
  "The hypothesis", TeX lines 903–907, and the recommendation after the
  remark). The plan note is design guidance, not a source of the statement.
