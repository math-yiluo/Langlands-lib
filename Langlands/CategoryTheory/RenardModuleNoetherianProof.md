# Proof of Renard's Noetherian comparisons for actual modules

This proof-only module proves the independently published closed statement
`Langlands.Renard.ModuleNoetherian.ModuleNoetherianStatement.{uR,uM}` from
`Langlands.CategoryTheory.RenardModuleNoetherianStatements`, for task
`a610ab9a-a388-4955-ada2-b0e75efdedc9`. The exported theorem is
`Langlands.Renard.ModuleNoetherian.moduleNoetherian`. Its complete type is
the aggregate `ObjectStatement.{uR,uM} ∧ CategoryStatement.{uR,uM}`, in that
order, with no section parameters or extra hypotheses. The target pair and
the imported source predicates are unchanged.

Worker 709 wrote the object comparison, the union-existence lemma and the
reduction of the category comparison to the actual-module finite-type
comparison. Worker 735 replaced the remaining premise with the published
finite-type proof and closed the aggregate. Integration reuses the identical
published union-existence lemma from `RenardModuleFiniteTypeProof`.

## Object comparison

For any unital ring `R : Type uR` and actual `M : ModuleCat.{uM} R`,
`object_iff` compares the unchanged source maximal-element predicate
`Langlands.Renard.IsNoetherianObject M` with Mathlib's algebraic
`IsNoetherian R M`. It uses the actual order equivalence
`ModuleCat.subobjectModule M` between categorical subobjects and
submodules, and Mathlib's `set_has_maximal_iff_noetherian`.

For the forward direction, pull a nonempty set of ordinary submodules
back through the order equivalence and choose a maximal categorical
subobject using the source predicate. Transport that witness to a
submodule. A strictly larger member would pull back to a member above
the maximal witness; the equality forced by source maximality contradicts
strict growth.

For the reverse direction, send a nonempty set of categorical subobjects
to submodules. Mathlib supplies a maximal member in the image. Pull its
membership witness back to a categorical subobject. If another member is
above it, monotonicity, absence of strict growth, antisymmetry and
injectivity of the order equivalence give the exact equality in the
source predicate. The witness belongs to the selected subset and need
not be its greatest element. `objectStatement` closes this argument over
all rings and modules, with independent `uR uM` and no extra premise.

The imported `Langlands.Renard.ModuleFiniteType.hasSubobjectUnions` shows
that every set of subobjects, including the empty set, has a least upper
bound. It takes the supremum of its image in the submodule lattice and
transports the supremum and its least-upper-bound property back through
the order equivalence.

## Category comparison

`category_of_finite_type` derives the category comparison from the closed
actual-module finite-type comparison at universes `uR, max uR uM`.
`categoryStatement` instantiates that premise with the published theorem
`Langlands.Renard.ModuleFiniteType.finiteType.{uR, max uR uM}` from
`Langlands.CategoryTheory.RenardModuleFiniteTypeProof`. That theorem
compares the source finite-type predicate with `Module.Finite R M`. Its
converse direction uses the general chain-to-finite-cover theorem
`Langlands.Renard.finiteTypeFiniteSubcover` from
`Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcover`. This module
uses both by Lean name and does not reprove either.

From the categorical property to ring Noetherianity: take the lifted
regular module `ModuleCat.of R (ULift.{uM} R)`, which lies in
`ModuleCat.{max uR uM} R` and is finitely generated. The finite-type
comparison makes it source-finite-type, and the category property then
makes it source-Noetherian. `object_iff` makes it algebraically
Noetherian, and transport along `ULift.moduleEquiv : ULift.{uM} R ≃ₗ[R] R`
gives left Noetherianity of the ring.

Conversely, assume the ring is left Noetherian. The imported
`Langlands.Renard.ModuleFiniteType.hasSubobjectUnions` gives the all-unions
conjunct of the source category predicate. Given a
source-finite-type module, the finite-type comparison makes it finitely
generated. Mathlib's instance for finite modules over a left Noetherian
ring makes it algebraically Noetherian, and `object_iff` translates this
back to the source predicate.

`moduleNoetherian_of_finite_type` is the same reduction for the aggregate.
`moduleNoetherian` pairs `objectStatement` with `categoryStatement` and
proves the exact target.

## Source correspondence and scope

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant pages are A.I.2–A.I.3, printed 248–249 (PDF 254–255). The
category/ring claim is the second sentence of the example on printed page
249 (PDF 255). The object comparison is an internal correspondence result
for the source maximal-element definition. The global unital-module
convention is on printed page 6 (PDF 12): `M(A)` is the full subcategory
of unital modules, which is what `ModuleCat R` models. Worker 709 and
Worker 735 each read PDF 254–255 and the convention on PDF 12 on
28 October 2026.

The exact target Markdown and the unchanged imported source-definition
pair record the retained wording repairs. A maximal member of the
nonempty subset is selected, chains are nonempty, properness is
inequality with top, and the cover equation uses the ambient object.
These are internal diagnoses, not author-issued errata. The implemented
proof goes through Mathlib's submodule order and Noetherian-module results.
It does not claim to reproduce proofs from Renard's references [25] or
[37].

All modules are ordinary unital left modules over arbitrary unital rings,
including noncommutative and zero rings. The object theorem adds no
finite-generation, ring Noetherianity, countability, field, nontriviality
or dimension assumption. The category comparison keeps carrier universe
`max uR uM`, which contains the lifted regular module. The source
Noetherian-category predicate includes union existence and quantifies
over source-finite-type objects. Mathlib's different category-wide
Noetherian predicate is not used.

Categories of possibly nonunital actions, general categorical criteria,
localization and the final C.II proposition remain separate obligations.
