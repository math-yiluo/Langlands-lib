# Finite Banach pushout and the size of its spectrum

This module isolates a finite Banach base change prerequisite for unrestricted
analytic étale pointwise lifting. `FiniteBanachPushoutStatement` is a
proposition that this module does not prove; the theorem `finiteBanachPushout`
in `FiniteBanachPushout/Proof` proves it. The module proves a special case and the stated consequences
conditionally on that proposition; it does not prove unrestricted pointwise
lifting.

## The base change statement

For a complete ultrametric normed field `K : Type u`, let `A`, `B`, and `C` be
actual presented affinoid algebras over `K`. Let `f : A → B` and `g : A → C` be
arbitrary bounded `K`-algebra maps. The statement says that if `f` is finite
Banach, then the original second map

`AffinoidPushout.rightMap f g : C → AffinoidPushout.algebra f g`

is finite Banach. The target is the existing closed quotient of the weighted
Tate algebra on the appended variables, with the existing coefficient
identification relations. No substitute algebra or supplied pushout is used.

The predicate `BoundedAlgHom.IsFiniteBanach` retains its published meaning:
there is a finite tuple of generators for which the finite coefficient map has
preimages with a uniform positive norm bound. Algebraic module finiteness alone
is not the conclusion. The statement imposes no nontrivial valuation, strict
radius, reducedness, nonzero-algebra, or nonempty-spectrum assumption.

## Implemented special case

`rightMap_isFiniteBanach_of_isAdmissibleEpi` proves the conclusion when `f` is an
admissible epimorphism. The existing `rightMap_isAdmissibleEpi` theorem gives
norm-controlled preimages for the unchanged second pushout map. These are
coefficients for the single generator `1`. The source coefficient vector has
the same norm as its sole entry, giving the required finite Banach bound.
This special case does not prove the statement for arbitrary finite Banach
maps.

## Implemented size consequences

`BoundedAlgHom.small_spectrum_of_finite` concerns general bounded maps of
normed algebras over an ultrametric normed field. If the underlying ring map is
finite and its target spectrum is `z`-small, its source spectrum is `z`-small.
Here the direction is that of the contravariant spectrum map: for `f : R → S`,
smallness of `BanachSpectrum R` implies smallness of `BanachSpectrum S`.
The universe `z` is independent of the field and both algebra universes.

The proof uses the existing `finite_fibre` theorem. Each fibre is equivalent
to a finite type `Fin n`, so it is small in every universe. A source point
injects into the dependent sum over target points of their fibres. The
dependent sum is small, and an injection into it proves smallness of the
source spectrum. This argument also covers empty spectra.

`finite_fibre_rightMap_of_finiteBanachPushout` applies the finite ring-map
consequence of the proposed finite Banach base change to the existing finite
fibre theorem. `small_spectrum_of_finiteBanachPushout` then applies the general
size lemma to the second pushout map. Both require
`FiniteBanachPushoutStatement K` as an explicit premise.

These results explain the size role of the prerequisite. If an affinoid chart
of a small analytic space is the changed base, finiteness of the second
pushout map would allow its spectrum to be represented in that same small
universe. This module does not construct a transported atlas, establish
étaleness of a base changed analytic map, or assemble a lifting object.

## Provenance

This is internal derived infrastructure. The statement is a proposed
stability property of the existing actual bounded pushout and finite Banach
definitions, isolated to address a universe obstacle in the analytic
pointwise lifting construction. The proof of the special case reuses the
published admissible pushout theorem without a new original-source claim.
The size proofs use the published finite fibre theorem and Mathlib's
`Small` API. No external theorem is cited as proving the general finite
Banach base change proposition.
