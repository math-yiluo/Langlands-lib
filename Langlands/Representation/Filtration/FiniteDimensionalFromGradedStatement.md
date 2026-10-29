# Finite dimensionality from the graded quotients of an actual filtration

Author: Worker 1022. Provenance: internal elementary linear algebra.

The proposition definition
`Langlands.ObjectRepFiltration.FiniteDimensionalFromGradedStatement.{uK,uG,uV}`
states a property of the Library's actual representation filtrations. This
pair states the claim only and does not prove it.

## Statement

The proposition ranges over every field `k : Type uK`, every monoid
`G : Type uG`, every representation `A : Rep.{uV} k G`, every natural number
`n`, and every filtration `s : ObjectRepFiltration A n`. The coefficient,
monoid and carrier universes are independent. Its only hypothesis is that
`FiniteDimensional k (s.gradedRepresentation i)` holds for every `i : Fin n`.
Its conclusion is `FiniteDimensional k A`. In both places this refers to the
`k`-vector space structure of the representation's carrier. The action of `G`
plays no role in either finite-dimensionality condition.

No further hypothesis is made. In particular, `A` and the intermediate steps
of `s` are not assumed finite-dimensional. `G` is only a monoid; it need not
be a group or finite. Nothing assumes a splitting of the filtration,
irreducible or nonzero graded quotients, a topology, or smoothness. Repeated
steps and zero graded quotients are allowed.

## The filtration and its graded quotients

`ObjectRepFiltration A n` and `gradedRepresentation` are imported unchanged
from `Langlands.Representation.Filtration.ObjectDefinitions`. A filtration has
`n + 1` actual `G`-invariant subspaces `s.subrepresentation j`, for
`j : Fin (n + 1)`, which increase with `j`. Its first step
`s.subrepresentation 0` is `⊥`, and its last step
`s.subrepresentation (Fin.last n)` is `⊤`, all of `A`.

For `i : Fin n`, the carrier of `s.gradedRepresentation i` is the quotient
module

`↥(s.subrepresentation i.succ).toSubmodule ⧸ (s.subrepresentation i.castSucc).toSubmodule.comap (s.subrepresentation i.succ).toSubmodule.subtype`.

Its numerator is the upper step, as a vector space in its own right. Its
denominator is the pullback of the lower step along the inclusion of the upper
step into `A`. Monotonicity puts the lower step inside the upper one, so this
denominator is the lower step itself, viewed inside the upper step. The graded
quotient is therefore the usual successive quotient `F_{i+1} / F_i`. Its
`k`-module structure is the quotient module structure. Both identifications
hold by definitional unfolding through `RepSubfunctor.quotientObj` and Mathlib's
`Rep.quotient`.

## Zero-length case

When `n = 0`, the hypothesis is vacuous. The first and last steps then
coincide, so `⊥ = ⊤` and `A` is zero. The proposition still asserts
`FiniteDimensional k A` in this case, which holds for the zero space.

## Provenance and rationale

This is an internal algebraic interface, not a transcription of a literature
theorem. It is a prerequisite for the finiteness of normalized parabolic
induction coinvariants, task `c1d64772-179e-4070-89c8-d0fd55df38d7`. That
task's filtration has graded quotients that are known to be finite-dimensional.
What is missing there is the elementary fact that this property passes to the
filtered vector space.

The mathematical rationale is induction along the steps. The zero step is
finite-dimensional. If `F_i` and `F_{i+1} / F_i` are finite-dimensional, so is
`F_{i+1}`, as an extension of one finite-dimensional space by another. The last
step is all of `A`. This paragraph is the rationale only. A Lean proof of this
exact proposition is a separate obligation after this statement is published.
