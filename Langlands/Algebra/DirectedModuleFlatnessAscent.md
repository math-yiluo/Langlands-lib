# Flatness ascent through a directed system of rings and modules

`Langlands.Algebra.directedModuleFlatnessAscent` proves the exact proposition
`Langlands.Algebra.DirectedModuleFlatnessAscentStatement`. The theorem keeps
five independent universes for the index, component rings and modules, and
target ring and module. The closing declaration explicitly declares those
universes in the same order as the published statement; its complete unapplied
constant has that ordered five-universe type. It uses the supplied target action and both actual
comparison maps of the published `DirectedModuleSystem`.

The helpers in `DirectedModuleFlatnessAscentProof` implement the equational
criterion argument. `finite_lift` chooses component representatives of a finite
family and moves them to one common upper bound. `map_trivial_relation` applies
a ring homomorphism to the relation's coefficient matrix and the compatible
semilinear additive map to its solution vectors; additivity and compatibility
with scalar multiplication preserve the two equations.

`flat_of_representatives` lifts the coefficients and vectors of a finite relation
in the target to a common stage. The eventual-zero hypothesis makes that
relation vanish at a later stage. A further flat stage supplies a trivial
relation by Mathlib's equational criterion. Mapping that solution into the
target and applying the converse criterion proves target flatness.

`flat_of_colimit` obtains ring and module representatives from surjectivity
of the actual comparison maps. Additive comparison injectivity and
`AddCommGroup.DirectLimit.of.zero_exact` give eventual vanishing. Eventual
flatness provides a flat stage above any specified stage. Ring comparison
injectivity is available in the statement but not needed by this argument.

The final wrapper supplies these helpers with `D.base`, `D.obj`, the original
transitions and cocone maps. Their semilinearity is exactly `map_smulₛₗ` for
`D.map` and `D.ιM`; the explicit additive `DirectedSystem` instance is inherited
from `D.directed`. The two bijectivity hypotheses are precisely `D.IsColimit`.
No local, finiteness, Noetherian, tensor-transition, or transition-injectivity
assumption is added. The proof is internal content derived from the pinned
Mathlib equational criterion and direct-limit APIs, not a separate numbered
literature theorem. It proves a supporting flatness ascent result and does
not itself prove 05UV or the existence of approximation systems.

The auxiliary theorem `LocalModuleSystem.flat_of_eventually_flat` applies
the generic result to the published `toDirectedModuleSystem` adapter. Its
hypothesis is the existing `E.IsColimit`, and its component actions are the
published scoped restrictions `LocalModuleSystem.objBaseModule` from
`LocalApproximationResidueFiber`. These actions are definitionally the ones
inside the adapter. The base-ring and additive comparison maps are
definitionally those already supplied by the adapter, so `E.IsColimit`
provides their bijectivity. The corollary keeps all seven index, component
and target universe levels independent. It uses neither the approximation
predicate's finiteness clauses nor any residue-fibre assertion.
