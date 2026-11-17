# Proposition 4.8 under the exact Weil stabilizer condition: datum and validity predicates

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerData`,
namespace `Langlands.Global.Harris`.

The module gives the hypotheses of Harris 1998, Proposition 4.8 (printed
p.201), and the validity predicates of the Library's induction for it, in the
form where the auxiliary character `χs` satisfies Harris's condition (4.12)
instead of general position. Each of the five definitions is a published
definition with **exactly one conjunct changed**. No published declaration is
modified.

## The changed conjunct

In each of the first, third and fourth definitions below, the published conjunct

```
IsInGeneralPosition F F' (weilCharacter F e F' χs)
```

(in the problem-bundle versions: `IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)`)
is replaced, at the same position, by

```
GeneralPosition.HasExactWeilStabilizer F F' (weilCharacter F e F' χs)
```

(resp. `GeneralPosition.HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)`).
`HasExactWeilStabilizer` is the published predicate of
`Langlands/Global/Arithmetic/GeneralPositionStatement.lean` (line 107): for
`χ` a character of `W_{F'}` and `χ̃` its restriction to `W_{F̃}`
(`closureRestriction`, `F̃` the Galois closure of `F'/F`), an element
`g ∈ W_F` satisfies `g(χ̃) = χ̃` (action `g(χ̃)(x) = χ̃(g⁻¹ x g)`) if and only
if `g ∈ W_{F'}`. The second and fifth definitions change only the name of the
predicate they call.

## Declarations

| New declaration | Published declaration | What changes |
| --- | --- | --- |
| `IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ` | `IsProposition48Datum` (`HarrisSetup.lean`, line 191) | Conjunct 14 of 19 (published line 201): `IsInGeneralPosition F F' (weilCharacter F e F' χs)` ↦ `HasExactWeilStabilizer F F' (weilCharacter F e F' χs)` |
| `Proposition48Problem.IsExactStabilizerValid Q` | `Proposition48Problem.IsValid` (`HarrisProposition48InductionData.lean`, line 65) | Second conjunct: `IsProposition48Datum Q.e Q.χ Q.χs Q.K₀ Q.P Q.Ps Q.ξ` ↦ `IsProposition48ExactStabilizerDatum Q.e Q.χ Q.χs Q.K₀ Q.P Q.Ps Q.ξ` (this carries the one changed conjunct of the datum) |
| `Proposition48Problem.IsExactStabilizerValidAtParity Q b` | `Proposition48Problem.IsValidAtParity` (`HarrisProposition48ParityData.lean`, line 19) | Conjunct 15 of 20 (published line 28): `IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)` ↦ `HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)` |
| `Proposition48Problem.IsAuxiliaryExactStabilizerValidAtParity Q b` | `Proposition48Problem.IsAuxiliaryValidAtParity` (`HarrisProposition48AuxiliaryData.lean`, line 18) | Conjunct 9 of 13 (published line 24): the same replacement |
| `Proposition48Problem.IsAuxiliaryExactStabilizerValid Q` | `Proposition48Problem.IsAuxiliaryValid` (`HarrisProposition48AuxiliaryData.lean`, line 29) | Body `Q.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1)` ↦ `Q.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1)` |

Every other conjunct is kept, in the published order: the split imaginary
quadratic field `K₀`, the scalar tower and normal closure `L` of `E'/E`, the
places above `p` with compatible completion maps and unique places of `L` above
them and their conjugates, the distinctness of the two places (in the
two-place predicates), the algebraicity at the given parity, relative
regularity, conjugate inversion, and the prescribed local components. The
binders, implicit and instance arguments and universes of the datum are those
of `IsProposition48Datum` (the same `variable` block: `{p} [Fact p.Prime] {F}
{F'} {E E' L}`, the field, number-field, algebra and CM instances, then `e χ χs
K₀ P Ps ξ`). The four predicates take `Q : Proposition48Problem.{uF}` (and
`b : ℕ` where the published one does).

A private audit (not submitted) checked mechanically, for all five
definitions and for the restated proposition of the sibling module, that the
published value with the one constant replaced (`IsInGeneralPosition` ↦
`HasExactWeilStabilizer`, or `IsProposition48Datum` ↦
`IsProposition48ExactStabilizerDatum`, or `IsAuxiliaryValidAtParity` ↦
`IsAuxiliaryExactStabilizerValidAtParity`) is structurally equal to the new
value, that the replaced constant occurs exactly once in the published value,
that the two swapped constants have the same type, and that the type, universe
parameters and reducibility are the same.

## Bridge theorems

The module also proves that each exact-stabilizer predicate implies the
published one:

- `IsProposition48ExactStabilizerDatum.isProposition48Datum`,
- `Proposition48Problem.IsExactStabilizerValid.isValid`,
- `Proposition48Problem.IsExactStabilizerValidAtParity.isValidAtParity`,
- `Proposition48Problem.IsAuxiliaryExactStabilizerValidAtParity.isAuxiliaryValidAtParity`,
- `Proposition48Problem.IsAuxiliaryExactStabilizerValid.isAuxiliaryValid`.

Each proof destructures the conjunction, keeps every conjunct, and replaces
the stabilizer conjunct by its image under the published theorem
`Langlands.Global.generalPositionOfExactStabilizer`
(`GeneralPositionOfExactStabilizerProof.lean`, line 48), which proves
`HasExactWeilStabilizer F F' χ → IsInGeneralPosition F F' χ`. They use only
the standard axioms. With them, the published general-position inputs of the
induction (rank one, parity normalization and untwist, the Mackey step) apply
unchanged to exact-stabilizer problems.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8: printed p.201 (PDF p.25), with the setup of Section 4 on
  pp.200–201. Condition (4.12): in the proof of Lemma 4.7, printed p.204
  (PDF p.28), the proof running over pp.204–206: with `G = Γ_F`, `H = Γ_{F'}`
  and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`, "a sufficient condition for irreducibility of
  `Ind_H^G χ(*)` is that `H` is the stabilizer in `G` of `χ̃(*)`:
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}` (4.12)". The Library's
  `HasExactWeilStabilizer` reads this on the Weil side.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455, source
  `henniart-2000-simple-proof`: §3.4, condition 3) (p.449) and §3.6, Lemme 3
  (p.451), the form of the condition that his globalization supplies.
- Design: operator plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8, Remark 4.2 (`rem:noDrinfeld`, TeX lines 859–894) and the
  paragraph "The remark and the Library's statements" (TeX lines 897–912),
  whose item "The hypothesis" (lines 903–907) asks for `HasExactWeilStabilizer`
  in place of `IsInGeneralPosition` in the datum and in the validity
  predicates of the induction.

## Provenance and what is not claimed

The datum is Harris's hypotheses of Proposition 4.8 with his condition (4.12)
in place of "in general position"; Harris constructs auxiliary characters
satisfying (4.12) in the proof of Lemma 4.7 and deduces general position from
it. The four validity predicates are internal: they are the Library's
induction predicates (derived formalization choices, see the published
Markdown of the three modules cited above) with the same single change. This
module asserts no existence, inheritance or solution statement; the
inheritance statements are in
`HarrisProposition48ExactStabilizerInheritanceStatement`, unproved.
