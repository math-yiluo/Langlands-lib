# Noetherianity of a unitization and its scalar-projection kernel

This proof module proves the published aggregate
`Langlands.Algebra.UnitizationNoetherian.UnitizationNoetherianStatement`
in theorem `unitizationNoetherian`. Its two universes `uR` and `uA` are
independent. The proof imports the statement and leaves its pair unchanged.
The aggregate includes the general kernel criterion, its specialization
over a Noetherian scalar ring, and its specialization over a field, in that
order.

Write `U = Unitization R A` and
`I = RingHom.ker (Unitization.fstHom R A)`. The hypotheses are a
commutative unital scalar ring `R`, a possibly noncommutative nonunital
ring `A`, an ordinary `R`-module structure on `A`, and the two scalar
compatibility laws making its multiplication bilinear. The kernel ideal
has its actual inherited regular left `U`-module structure. No unit or
Noetherianity assumption on `A`, finite dimension, countability or
nontriviality assumption is added.

The helper `noetherian_iff_kernel` proves the general equivalence.
In the forward direction the scalar projection is surjective, with
preimage `Unitization.inl r` for each scalar `r`. Noetherianity descends
along that surjective ring homomorphism. The kernel ideal is Noetherian
as a submodule of the Noetherian regular module.

For the reverse direction the proof gives `R` the actual `U`-module
structure obtained by composing its regular action with the scalar
projection. It constructs the compatible scalar tower explicitly.
Noetherianity of the regular `R`-module then implies Noetherianity of
this `U`-module by `isNoetherian_of_tower`. The linear scalar projection
`p : U →ₗ[U] R` has kernel `I`, which is the range of the actual subtype
inclusion of `I`. The exact-sequence theorem
`isNoetherian_of_range_eq_ker` therefore proves Noetherianity of `U`.

`kernelCriterion` closes all parameters of this helper.
`noetherianScalarCriterion` removes the scalar-ring conjunct using its
Noetherian instance. `fieldCriterion` applies that specialization using
Noetherianity of every field. `unitizationNoetherian` combines these
three complete propositions. No custom unitized action on `A` or
stable-subspace lattice is constructed here.

The result is derived internal algebra motivated by Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, I.2.1 (printed page 14 / PDF page 20) and the final
proposition of C.II (printed page 279 / PDF page 285). The registered
source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These exact criteria are not attributed to a numbered book assertion.
The implemented proof uses the scalar-coordinate exact sequence.
It does not settle the book's nonunital Noetherian convention, compare
source-compatible stable subspaces, or prove the localization theorem.

The parent retains the separate comparisons for source-compatible actions,
stable-subspace lattices, finite generation and the nonunital Noetherian
convention, as well as the actual C.II localization proposition.

Worker 709 authored the proof; Worker 702 checked the complete declaration
types and prepared this proof module for independent review.
