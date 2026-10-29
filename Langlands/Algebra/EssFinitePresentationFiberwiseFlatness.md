# Fibrewise flatness for essentially finitely presented local algebras

`Langlands.Algebra.essFinitePresentationFiberwiseFlatness` proves exactly
`Langlands.Algebra.EssFinitePresentationFiberwiseFlatnessStatement`, the
criterion of Stacks Project, Lemma 10.128.8, tag
[00R7](https://stacks.math.columbia.edu/tag/00R7).

For local homomorphisms of local rings `R → S → T`, assume that both `S` and
`T` are essentially finitely presented over `R`. Let `M` be a nonzero finitely
presented `T`-module, with its compatible restricted actions. If `M` is flat
over `R` and its actual tensor residue fibre is flat over
`F = S ⊗[R] IsLocalRing.ResidueField R`, then `S` is flat over `R` and `M`
is flat over `S`. The theorem retains the four independent ambient universes
and every quantified action of the published statement. It adds no supporting
premise or Noetherian assumption.

## Implemented proof

The final theorem first applies the published
`essFinitePresentationTowerCancellation` to obtain essential finite presentation
of `T` over `S`. It applies `localModuleTowerApproximationExistence` to obtain one
directed system `R_i → S_i → T_i`, with modules `M_i`, approximating the entire
tower and `M`. Its index and component carriers lie in the maximum of the four
ambient universes; the ambient universes themselves remain independent.
The published `localTowerResidueFiberApproximation` proves that the actual
package `E.fiberModuleSystem` is an approximation as well. Thus all approximation
properties used below are established by imported proofs and the original
hypotheses.

The helper `rtModule_isApproximation` extracts the composite-arrow approximation
`R_i → T_i, M_i`. Its base and top ring colimits are projections of the
synchronized colimits. Composition supplies essential finite type of `T_i`
over `R_i`, and the original tower supplies the finite-module and transition
clauses.

The imported `LocalModuleSystem.eventually_flat_of_descent_and_propagation`
from `LocalFiberInjectivity` applies the published
`localApproximationFlatnessDescent` (the 00R6 criterion) to get one flat stage.
The scalar tower identifies the ambient action with the restriction required
by that theorem: `Module.ext'` uses `IsScalarTower.algebraMap_smul` to prove
the equality of the module structures. The published
`localApproximationFlatnessPropagation` then propagates flatness to every later
stage, using the approximation's actual prime-localization and module
base-change clauses. Applied to the composite-arrow approximation,
`eventually_flat_over_base` gives eventual flatness of `M_i` over `R_i`.

For the second application, put `κ_i = IsLocalRing.ResidueField R_i`,
`F_i = S_i ⊗[R_i] κ_i`, `G_i = T_i ⊗[R_i] κ_i`, and
`N_i = κ_i ⊗[R_i] M_i`. These are the published fibre package's carriers,
transitions and actions. The helper `eventually_flat_over_lower_fiber` applies
the same descent and propagation argument to `F_i → G_i, N_i`.
The published `residueFiberFiniteness`, applied to `T` over `S` and `M` over
`T`, supplies essential finite presentation of the ambient fibre arrow and
finite presentation of the raw residue module. The inverse of
`targetLowerFiberModuleEquiv` transports the given flatness of `F ⊗[S] M`
to the raw ambient residue module. After descent, the equality
`fiberModuleSystem_objBaseModule` identifies the package's restricted action
with the raw `F_i`-action. This gives eventual flatness of `N_i` over `F_i`.

The helper `eventually_nontrivial` represents a fixed nonzero element of `M`
in the actual additive direct limit. At every later stage its representative
still maps to that same nonzero element, so every later `M_i` is nontrivial.
This uses surjectivity and cocone compatibility, without transition injectivity.

The helper `eventually_stagewise_flat_of_criterion` combines the two flatness
tails and the nontriviality tail at a common directed bound. Essential finite
type over the integers, and then along the two component arrows, gives the
three Noetherian ring instances. The published lower fibre-module equivalence
transports flatness of `N_i` to the precise tensor fibre used by
`noetherianFiberwiseFlatness` (00MP). That theorem yields flatness of `S_i`
over `R_i` and of `M_i` over `S_i` at every stage of the common tail.

The helper `flat_of_eventually_stagewise_flat` applies the published
`LocalModuleSystem.flat_of_eventually_flat` twice. For `S` over `R`, the regular
module construction and `regularModuleSystem_isColimit` convert the actual
ring colimit into the required additive colimit. An identity linear equivalence
identifies its restricted component action with the original algebra action;
`Algebra.smul_def` checks scalar compatibility. For `M` over `S`, the original
upper module colimit gives the second application directly. Both conclusions
therefore ascend through the actual varying-base systems.

The helpers `flat_of_fiber_tail` and `flat_of_actual_fiber_approximation` compose
these steps. The final theorem supplies their synchronized and fibre
approximation inputs using the published existence and preservation theorems.
The other helpers in this module are internal assembly lemmas, derived from the
published definitions and the imported theorems; they are not additional
literature claims.

## Source and localization conventions

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
`00R7.html`, Lemma 10.128.8, lines 174–239, in
`literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The statement is at lines 174–198; the approximation, two descent applications,
and Noetherian criterion appear at lines 202–236.

The source's final plain tensor equalities omit the localizations occurring in
the preceding systems. This implementation retains the actual localization
maps for descent and propagation and uses varying-base colimit ascent for the
last step. It does not require those equalities. The source's quotient fibres
are represented by the published tensor fibres with their explicit scalar
compatibilities and linear comparisons.

## Development verification

A development Lake build and complete declaration inspection succeeded with
zero errors and warnings. The inspected declaration has exactly
`EssFinitePresentationFiberwiseFlatnessStatement.{uR, uS, uT, uM}` as its type,
with the independent level parameters `uR`, `uS`, `uT`, and `uM`. Its only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Official exact-target
validation, independent semantic review, and Library publication are recorded
separately by the submission process.
