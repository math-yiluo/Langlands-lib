# Local central transpose-to-primal conversion

Authors: Worker 429 (proof implementation) and Worker 51 (adaptation,
verification and submission). The finite-fixed-space route follows discussions
among Workers 84, 728 and 429.

The theorem `Langlands.admissibleCentralDualToPrimal` has the complete unapplied
type `Langlands.AdmissibleCentralDualToPrimalStatement.{uG,uA,uV}`, imported from
`Langlands.Representation.Exponents.AdmissibleCentralDualToPrimalStatement`.
The group, central parameter group and carrier universes remain independent.
The statement and all its imported Lean/Markdown pairs are unchanged.

Let `G` be a topological group in which every open subgroup contains a compact
open subgroup, `A` an abstract commutative group, `V` a complex vector space,
`ρ : Representation ℂ G V` an admissible representation and
`c : A →* Subgroup.center G`. Write
`ρ_A = ρ.comp ((Subgroup.center G).subtype.comp c)`. From a nonzero ordinary
eigenfunctional in
`commutativeCharacterSpace (commutativeTranspose ρ_A) χ 1`, the theorem obtains
one natural number `k` and one nonzero `v : V` such that
`((ρ_A a - (χ a : ℂ) • 1) ^ k) v = 0` for every `a : A`.
The character is the same `χ`; neither inversion nor conjugation occurs.
The functional is in the full algebraic dual and need not be smooth.

## Finite-dimensional argument

The private lemma `finite_central_dual_to_primal` treats a representation of
`A` on a finite-dimensional complex vector space, with a nonzero transpose
eigenfunctional `φ` of character `χ`.

It equips `A` temporarily with the discrete topology. Its representation is
then locally constant, and the span of its operators is finite dimensional
because it is a subspace of the finite-dimensional endomorphism space.
The spanning clause of the published
`Langlands.finiteActionCommutativeSpectrum` says that the supremum of the
generalized character subspaces indexed by open-kernel ordinary
eigencharacters is the whole carrier. If `φ` vanished on every one of these
subspaces, its kernel would be the whole carrier. Thus some character `ψ`
has a generalized vector `w` with `φ w ≠ 0`. Membership supplies a single
natural number `k` such that every `ψ`-defect power of order `k` kills `w`.

The shared helper `Langlands.ScalarLayer.pow_sub_smul_apply_of_eigen`, imported
from [EigenvectorDefect](../../LinearAlgebra/EigenvectorDefect.md) and proved by
induction on the power, calculates a defect power on an ordinary eigenvector.
Applied to the transpose eigenfunctional, and combined with
the published `commutativeTranspose_defect_pow_apply`, it gives, for each
`a : A`,

`((χ a : ℂ) - (ψ a : ℂ)) ^ k * φ w = 0`.

Since `φ w ≠ 0`, the scalar power is zero, and hence `χ a = ψ a` in `ℂ`.
This also rules out the order-zero case. Substituting these equalities
into the generalized-vector equations yields the generalized-eigencharacter
conclusion for `χ` on the finite carrier. The topology
introduced in this lemma is local to its proof and yields no assertion
about an independently supplied topology on `A`.

## Localization and inclusion

The closing theorem chooses a nonzero transpose eigenfunctional `φ` from the
hypothesized nonzero subrepresentation, and then chooses `v : V` with
`φ v ≠ 0`. Smoothness, the first clause of `IsAdmissible ρ`, gives an open
subgroup `H` fixing `v`. The cofinality premise gives a compact open subgroup
`K ≤ H`, so `v` is also `K`-fixed. The compactness certificate is not needed
subsequently: the Library's admissibility predicate makes the fixed space of
every open subgroup finite dimensional.

The proof defines the actual subrepresentation `S` of `ρ_A` whose underlying
submodule is `fixedVectors ρ K.toSubgroup`. For `a : A` and `k ∈ K`,
centrality gives `ρ k (ρ (c a) w) = ρ (c a) (ρ k w)`. Consequently
`ρ (c a)` preserves the fixed space. Restricting `φ` along its inclusion
gives a transpose eigenfunctional on `S` with character `χ`. It is nonzero
because its value at the fixed vector `v` is nonzero.

Applying the finite-dimensional lemma produces `k` and a nonzero `w : S`.
The private helper `centralDualToPrimal_defect_pow_coe` proves by induction
that the inclusion of a subrepresentation commutes with each power of each
character-defect operator. Thus the same `k` and the image of `w` in `V`
satisfy the conclusion for every `a`. The image is nonzero because subtype
inclusion is injective.

## Provenance and scope

This is project-internal derived algebra, not a translation of a numbered
literature result. Worker 429 wrote the reused
`CentralDualToPrimalProbe.lean` in revision 3 of statement task
`529397b1-c0d9-41a3-95a5-049391c47589`. Worker 51 preserved its proof bodies,
renamed the probe theorem and private helper prefixes, and prepared this
focused module and its documentation. The finite-spectrum and scalar
cancellation route adapts the argument of
`Langlands.ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent`;
the localization to one fixed space follows discussions with Workers 84 and
728. This module imports the published finite-spectrum proof directly. The
existing irreducible-source classification results retain their types and proofs.
At integration, the identical eigenvector-defect helper was shared with that
assembly through `Langlands.LinearAlgebra.EigenvectorDefect`; its existing public
name, statement and proof were preserved, and this module's private copy was
removed.

No irreducibility, finite length, finite generation, global finite operator
span, global finite spectrum, supplied primal vector or scalar central
character is assumed. No topology on `A`, continuity of `c`, or open kernel
of `χ` is assumed. The theorem gives one generalized vector, not a bound on
the whole generalized component or a decomposition of the original carrier.
It supplies no analytic exponent criterion, opposite-to-upper transport,
scalar-subquotient detector, Jacquet admissibility or class inheritance,
cone bound, continuation, multiplicity comparison, composition series,
quotient or head theorem. The published reverse-direction theorem is not
restated.

## Validation, review and publication

The prescribed environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0 with the project's pinned
Mathlib). Worker 429's original probe and its reported development check
are unreviewed development material. This adaptation's own development Lake
check `f7d31b6d-8759-454b-aa5d-81ee2e147014` succeeded with zero errors and
warnings. Inspection reports the complete unapplied theorem as the named
statement with independent level parameters `uG`, `uA` and `uV`, and only
`propext`, `Classical.choice` and `Quot.sound`. A private direct assignment
of the unapplied theorem to that exact statement, together with `#check`
and `#print axioms`, also passed in development check
`8751b8fb-5f1a-4032-8e15-65804d0c5816`.

At preparation for staging, these are development results; the candidate has
not yet undergone independent semantic review or publication. Formal acceptance
additionally requires its own Lake build, exact-target and unchanged-input
checks, independent semantic review, and Library publication. Local compilation
alone does not establish any of those later statuses. The final candidate's
validation, review and integration records determine its subsequent status.
