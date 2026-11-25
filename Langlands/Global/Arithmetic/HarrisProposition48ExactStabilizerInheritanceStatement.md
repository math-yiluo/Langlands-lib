# Inheritance of the exact Weil stabilizer condition in the Proposition 4.8 induction

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerInheritanceStatement`,
namespace `Langlands.Global.Harris`.

Harris 1998, Proposition 4.8 (printed p.201) is stated in the Library as the
unproved `Proposition48Statement`. Its planned proof is a recursion on the
degree of the normal closure, with one-place validity predicates for the
problems of the recursion (`Proposition48Problem`). This recursion is not
carried out in Lean: its steps are stated as separate statements, among
them the explicitly conditional `Proposition48ReductionStatement`, whose
input statements are hypotheses and which is proved as `proposition48Reduction`
in `HarrisProposition48ReductionProof`. The
proof obligations that remain open are listed in
`HarrisProposition48Statement.md`. This module states two
facts that are needed to run that recursion under Harris's condition (4.12)
(proof of Lemma 4.7, printed p.204) in place of general position. The
condition passes from a problem to each of its Mackey children, and to its
parity-corrected problem. In both statements the general-position
validity of the new problem is a hypothesis. The conclusion upgrades it to
exact-stabilizer validity. **Neither statement is proved here.**

The predicates used are those of the sibling module
`HarrisProposition48ExactStabilizerData`:
`IsAuxiliaryExactStabilizerValidAtParity` is the existing
`IsAuxiliaryValidAtParity` with its one conjunct
`IsInGeneralPosition Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)` replaced by
`GeneralPosition.HasExactWeilStabilizer Q.F Q.F' (weilCharacter Q.F Q.e Q.F' Q.χs)`,
and `IsAuxiliaryExactStabilizerValid` is it at parity `[E':E] − 1`.

## `Proposition48ExactStabilizerMackeyInheritanceStatement.{uF}`

For all `Q R : Proposition48Problem.{uF}`, `b c : ℕ`,
`D : IntermediateField Q.E Q.L` and `a : Q.L ≃ₐ[Q.E] Q.L`:

```
Q.IsAuxiliaryExactStabilizerValidAtParity b →
Q.IsAuxiliaryMackeyChild D a R →
R.IsAuxiliaryValidAtParity c →
R.IsAuxiliaryExactStabilizerValidAtParity c
```

`D` is any intermediate field of `L/E`, not only a cyclic step of prime
degree, and the parities `b`, `c` are arbitrary. The child's general-position
validity `R.IsAuxiliaryValidAtParity c` is a hypothesis. The existing Mackey
step `Proposition48MackeyStepStatement` produces children with exactly this
validity, so it can be used unchanged and its children upgraded afterwards.
The conclusion differs from that hypothesis only in the stabilizer conjunct.
The statement is not a weakening of the Mackey step: that step chooses a
specific field `D` and proves general position of its children, while this
statement upgrades every child that is valid in the general sense.

### Why it is true

This is the argument of the plan note, Section 4.8, item "The hypothesis" (TeX
lines 903–907), transported along the place data of the child.

*Step 1: the condition only depends on the field side.* Suppose
`NormalizedReciprocity F e`. Then
`HasExactWeilStabilizer F F' (weilCharacter F e F' χ)` is equivalent to the
field-side form of (4.12): for `σ ∈ Gal(F̃/F)`, `σ` fixes `χ ∘ N_{F̃/F'}` if
and only if `σ ∈ Gal(F̃/F')`. Indeed, `NormalizedReciprocity` contains the
norm and conjugation squares of the reciprocity family
(`NormRelation`, `ConjugationRelation`, `ReciprocitySystem.lean` lines
225–248). By the norm square, the restriction of `weilCharacter F e F' χ` to
`W_{F̃}` corresponds to `χ ∘ N_{F̃/F'}` under the isomorphism
`W_{F̃}^{ab} ≅ F̃^×`. By the conjugation square, conjugation by `g ∈ W_F`
corresponds to the action of the image of `g` in `Gal(F̃/F)`. Since
`W_F → Gal(F̃/F)` is onto with kernel `W_{F̃}`, and `W_{F'}` is the preimage of
`Gal(F̃/F')`, the two conditions agree. The field-side form does not mention
`e`, and it is invariant under isomorphisms of the triple `F ⊆ F' ⊆ F̃` that
carry one character to the other.

*Step 2: the child's local data.* `Q.IsAuxiliaryMackeyChild D a R` gives ring
isomorphisms `e : R.E ≃ D` and `e' : R.E' ≃ D·a(E')` and an embedding
`j : R.L → Q.L`, compatible with the algebra maps. It also gives
`R.ξ = a(ξ) ∘ N_{D·a(E')/a(E')}` transported along `e'`, and says that the
child's auxiliary place `R.Ps.v` lies, through `e`, above `Q.Ps.v`. Let `ṽ` be
`Q.Ps.vTilde`, and identify `Q.L_ṽ` with `F̃` by `Q.Ps.isoTilde`. Since `Q.L`
has exactly one place above `Q.Ps.v`, so does `D`. Hence `e(R.Ps.v)` is the
place of `D` below `ṽ`. Since `R.L` has exactly one place above `R.Ps.v` (a
conjunct of the child's validity), `j` carries `R.Ps.vTilde` to the place of
`j(R.L)` below `ṽ`. Likewise `R.Ps.v'` corresponds to the place of `D·a(E')`
below `ṽ`. The automorphism `a` fixes `E`, so it permutes the places of
`Q.L` above `Q.Ps.v`. As there is only one, it fixes `ṽ`, and it induces an
element `ã ∈ Gal(F̃/F)`.

Write `F₁ ⊆ F̃` for the closure of `D`; it is an intermediate field of
`F̃/F`. The closure of `D·a(E')` is `F₁·ã(F')`, and the closure `M` of
`j(R.L)` is the Galois closure of `F₁·ã(F')` over `F₁`, because `R.L` is the
normal closure of `R.E'/R.E`. The child's own completion data
(`R.Ps.iso`, `R.Ps.isoTilde`, `R.Ps.IsCompatible`) identify the child's
triple `R.F ⊆ R.F' ⊆ R.F̃` with `F₁ ⊆ F₁·ã(F') ⊆ M`. Through these
identifications, `R.Ps.HasComponent R.ξ R.χs`, the formula for `R.ξ` and
`Q.Ps.HasComponent Q.ξ Q.χs` identify `R.χs` with
`χs^ã ∘ N_{F₁·ã(F')/ã(F')}`, where `χs^ã = χs ∘ ã⁻¹` is a character of
`ã(F')^×`. By Step 1, and because `NormalizedReciprocity R.F R.e` is a
conjunct of the child's validity, the child's stabilizer conjunct is the
field-side condition for this triple and character. It does not depend on the
choice of the abstract fields `R.F`, `R.F'`, of `R.e`, or of the
identifications, which are fixed by the child's validity.

*Step 3: the stabilizer.* Let `σ ∈ Gal(M/F₁)` fix
`χs^ã ∘ N_{M/ã(F')}`. Here the norm is taken through `F₁·ã(F')`, and
`N_{M/ã(F')}` means `N_{F₁·ã(F')/ã(F')} ∘ N_{M/F₁·ã(F')}`. Lift `σ` to
`σ̂ ∈ Gal(F̃/F₁)`. Composing with `N_{F̃/M}`, `σ̂` fixes
`χs^ã ∘ N_{F̃/ã(F')} = (χs ∘ N_{F̃/F'}) ∘ ã⁻¹`. This is the restriction of
`χs^ã` to the closure. By (4.12) for `Q` (field-side form, Step 1, using
`NormalizedReciprocity Q.F Q.e`), the stabilizer of this character in
`Gal(F̃/F)` is `ã·Gal(F̃/F')·ã⁻¹ = Gal(F̃/ã(F'))`. So
`σ̂ ∈ Gal(F̃/F₁) ∩ Gal(F̃/ã(F')) = Gal(F̃/F₁·ã(F'))`, and
`σ ∈ Gal(M/F₁·ã(F'))`. Conversely, every element of `Gal(M/F₁·ã(F'))` fixes
the character, because it is pulled back from `F₁·ã(F')`. So the child
satisfies (4.12). This is the plan note's sentence: "an element of `W_{F₁}`
that fixes the restriction of a conjugate `χ(*)^a` to the Weil group of the
Galois closure of `F₁ a(F')` over `F₁` fixes its restriction to `W_{F̃}`,
which is `χ̃^a`, and so lies in `W_{a(F')}` by (4.12), hence in
`W_{F₁ a(F')}`". All other conjuncts of the conclusion are conjuncts of
`R.IsAuxiliaryValidAtParity c`.

## `Proposition48ExactStabilizerParityInheritanceStatement.{uF}`

For all `Q : Proposition48Problem.{uF}`, `b : ℕ`, `ν : HeckeCharacter Q.E`
and `χs : FieldCharacter Q.F Q.F'`:

```
Q.IsAuxiliaryExactStabilizerValidAtParity b →
Q.IsAuxiliaryParityNormalization b ν χs →
(Q.withCharacters (Q.correctedCharacter ν) χs χs).IsAuxiliaryExactStabilizerValid
```

The existing `IsAuxiliaryParityNormalization` is kept unchanged. It contains
the general-position validity `IsAuxiliaryValid` of the corrected problem,
whose global character is `ξ · (ν ∘ N_{E'/E})` and whose auxiliary character is
the new `χs`. The conclusion upgrades the corrected problem to the
exact-stabilizer predicate at the original rank parity.

### Why it is true

The corrected problem has the same fields, place data and reciprocity family
as `Q`. Write `χs_Q` for the auxiliary character of `Q`. The component
conjuncts `Q.Ps.HasComponent Q.ξ χs_Q` (from the first hypothesis) and
`Q.Ps.HasComponent (ξ · ν ∘ N_{E'/E}) χs` (from the corrected validity),
together with the compatible completion maps of `Q.Ps`, give
`χs = χs_Q · (μ ∘ N_{F'/F})`. Here `μ` is the component of `ν` at `Q.Ps.v`
read on `F^×`. The component of `ν ∘ N_{E'/E}` at the unique place `v'`
above `v` is `ν_v ∘ N_{E'_{v'}/E_v}`, and `E_v ≅ F`, `E'_{v'} ≅ F'`. By the
norm square of the normalized reciprocity family, the Weil character of
`μ ∘ N_{F'/F}` is the restriction to `W_{F'}` of the character
`ψ = μ ∘ rec_F` of `W_F`. So the corrected auxiliary character is `χs_Q`
times the restriction to `W_{F'}` of a character of `W_F`. Its restriction to
`W_{F̃}` is `χ̃_Q · ψ|_{W_{F̃}}`, and `ψ|_{W_{F̃}}` is invariant under
conjugation by `W_F`. Hence `g ∈ W_F` fixes the new restriction if and only
if it fixes `χ̃_Q`. The stabilizer does not change, and (4.12) for `Q` gives
(4.12) for the corrected problem. All other conjuncts of the conclusion are
conjuncts of the corrected problem's `IsAuxiliaryValid`.

## What is not claimed

- Neither inheritance statement is proved here. They are proved as
  `proposition48ExactStabilizerMackeyInheritance` in
  `HarrisProposition48ExactStabilizerMackeyProof` and
  `proposition48ExactStabilizerParityInheritance` in
  `HarrisProposition48ExactStabilizerParityInheritanceProof`. The arguments
  above explain why the statements are expected
  to be true; they are not Lean proofs.
- Neither `Proposition48Statement` nor the restated
  `Proposition48ExactStabilizerStatement` (sibling module
  `HarrisProposition48ExactStabilizerStatement`) is proved.
  `Proposition48ExactStabilizerStatement` is a weaker proposition than
  `Proposition48Statement`: its datum hypothesis
  `IsProposition48ExactStabilizerDatum` is stronger than
  `IsProposition48Datum`, and the rest is identical. `Proposition48Statement`
  implies it through the theorem
  `Langlands.Global.generalPositionOfExactStabilizer`
  (`HasExactWeilStabilizer F F' χ → IsInGeneralPosition F F' χ`); the sibling
  module proves this implication as
  `proposition48ExactStabilizerStatement_of_proposition48Statement`.
- The arguments are written for this module from the plan note's design
  argument and Harris's (4.12). Harris does not state these inheritance
  facts. The plan note says that its Remark 4.2 "is an argument written here,
  not one taken from the literature".
- No existing declaration is changed. The general-position formulation and
  its Mackey step and parity statements stay as
  the fallback.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, source
  `harris-1998-local-langlands` (PDF page = printed page − 176).
  Proposition 4.8: printed p.201 (PDF p.25); its proof and the inherited
  conditions (i)–(iii): pp.201–203. Condition (4.12): proof of Lemma 4.7,
  printed p.204 (PDF p.28), the proof running over pp.204–206: with
  `G = Γ_F`, `H = Γ_{F'}` and `χ̃(*) = χ(*) ∘ N_{F̃/F'}`,
  `H = {g ∈ G | g χ̃(*) = χ̃(*)}`.
- Design: operator plan note `operator-external-inputs-plan-2026-11-16`,
  Section 4.8: Remark 4.2 (`rem:noDrinfeld`, TeX lines 859–894) and the
  paragraph "The remark and the Library's statements" (TeX lines 897–912),
  item "The hypothesis" (lines 903–907). The plan note is unreviewed design
  guidance.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455, source
  `henniart-2000-simple-proof`: §3.4, condition 3) (p.449), and §3.6,
  Lemme 3 (p.451). This is the unit-level form of the condition, which is
  unchanged by unramified twists.
