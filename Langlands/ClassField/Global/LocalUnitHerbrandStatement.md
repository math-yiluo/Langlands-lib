# Cohomology of the valuation units of number-field completions (statements)

Author: Worker 226.

This module states three propositions and proves nothing. They concern the published
`Langlands.ClassField.Global.localUnitsRepresentation v w` (module
`Langlands.ClassField.Global.LocalUnitCohomology`). This is the valuation units
`U_w = {x ∈ E_wˣ | v(x) = 1}` of the completion `E_w = w.adicCompletion E`, as a
representation of the local automorphism group
`Gal(E_w/F_v) = w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E` over the
lifted integers `NormalizedTwoCocycle.CoefficientScalars`. Cohomology is Mathlib's ordinary
`groupCohomology`. The local algebra `F_v → E_w` is the Library's scoped instance from
`Langlands.Global.AdelicFunctoriality.FiniteExtension`.

## `CyclicCompletionUnitHerbrand`

For number fields `F E : Type u` in a common arbitrary universe, `[Algebra F E]` and
`[IsGalois F E]`, a finite place `v` of `F`, a finite place `w` of `E` with
`[w.asIdeal.LiesOver v.asIdeal]`, and a cyclic local group (`[IsCyclic (Gal(E_w/F_v))]`):

`H¹(Gal(E_w/F_v), U_w)` and `H²(Gal(E_w/F_v), U_w)` are finite and
`Nat.card H² = Nat.card H¹`.

Since `H²` of a cyclic group is the Tate group `Ĥ⁰`, this says that the Herbrand quotient
is `h(U_w) = 1`. Finiteness is part of the conclusion, not a hypothesis. The degree-one
local extension is included.

## `UnramifiedCompletionUnitVanishing`

For the same number-field and place data with `[IsGalois F E]`, without a cyclicity
assumption, and with `w.asIdeal.ramificationIdx (𝓞 F) = 1`:

`H¹(Gal(E_w/F_v), U_w)` and `H²(Gal(E_w/F_v), U_w)` are both `Subsingleton`.

## `CompletionUnitHerbrandFromCohomologyExistence`

`Langlands.ClassFieldTheory.Local.CohomologyExistence.{u, u}` implies the conjunction
`CyclicCompletionUnitHerbrand.{u} ∧ UnramifiedCompletionUnitVanishing.{u}`. This is an
internal derived implication. It records that local invariant existence would suffice, and
it is not a claim that `CohomologyExistence` is proved.

## Universes

All fields live in one universe `u`, because `localUnitsRepresentation` and the valuation
sequence of `LocalUnitCohomology` use that interface. The global first inequality
`CyclicIdeleClassHerbrandQuotient.{u,v}` has independent universes. A consumer of these
local results there still needs a transport or generalization; this module does not
provide one.

## Provenance

The original statements are in E. Artin and J. Tate, *Class Field Theory* (2009), source
`artin-tate-2009-class-field-theory` (PDF page = printed page + 9). Chapter V §2,
printed p.12 (PDF p.21), recalls from local class field theory that
`h1(G_p, U_p) = h2(G_p, U_p) = e_p` for a cyclic local extension, `e_p` being the
ramification index, and that `e_p = 1` at almost all places. Section 3, printed p.13
(PDF p.22), uses this in the first inequality for number fields.
`CyclicCompletionUnitHerbrand` keeps the equality of the two finite orders but not the
value `e_p`. `UnramifiedCompletionUnitVanishing` is the case `e_p = 1`.

The Herbrand-quotient form `h(U_L) = 1` is J. S. Milne, *Class Field Theory* v4.03 (2020),
source `milne-2020-class-field-theory`, Chapter III, Lemma 2.5, printed p.104 (PDF p.113).

These are the statements requested by Worker 343's statement task
`f800fd97-8ac4-437e-bc18-1098d89f750d` (names as suggested there), formulated with the
actual Library representation.
