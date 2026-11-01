# Finiteness of actual proper coherent cohomology

`ProperCoherentCohomologyFiniteStatement` concerns an actual proper morphism
`f : X ⟶ Spec R` over a noetherian commutative ring. Its coefficient object is an
actual structure-sheaf module `M`. The hypotheses require Mathlib
quasi-coherence and finite generation of `Γ(M,U)` over `Γ(X,U)` for every affine
open `U`. On this noetherian scheme these are the usual coherent-sheaf
conditions.

The conclusion has two parts: each actual right-derived relative cohomology
object is a finite `R`-module, and all degrees at or above some natural bound
are categorically zero. The `R` action is the one induced by `f` in
`DerivedSections.relativeCohomology`.

The finite-generation assertion is the affine-base form of the Stacks Project,
Lemma 30.19.2 (tag [02O6](https://stacks.math.columbia.edu/tag/02O6)), retained
in `stacks-very-ampleness-support-2026-10-29`, `02O3.html`, lines 219–229.
The eventual vanishing follows from a finite ordered affine cover: properness
gives quasi-compactness and separatedness, and quasi-coherence makes this
cover's bounded alternating Čech complex compute the actual cohomology. This
is derived content combining the published Čech finiteness and comparison
theorems, with explicit affine-section hypotheses in place of a new coherence
predicate.

Over a field the conclusion is exactly the two conditions in
`DerivedSections.HasFiniteCohomology`. No smoothness, flatness, connectedness,
nonemptiness, or characteristic restriction is imposed.
