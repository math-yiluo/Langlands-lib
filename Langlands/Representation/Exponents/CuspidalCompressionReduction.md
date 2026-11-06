# Compression reduction through actual induced-cuspidal embeddings

This internal reduction proves pointwise and then representation-uniform
compression stability from the actual finite induced-cuspidal embedding
target and eventual stability on every normalized induction of an arbitrary
cuspidal object from the standard Levis. Both premises remain explicit.

The group and carrier universes `uG` and `uV` are independent. The finite
standard index type has universe `uG`, as for the actual simple-root index.
Intermediate carriers use `max uG uV`. The ambient group is locally compact
and nonarchimedean. The actual semidirect standard family, closed Levi and
radical subgroups, and inside-Levi semidirect decompositions are supplied.
Compression is the actual compact average after the action of the supplied
element `g`, on vectors fixed by the compact open subgroup `K`.

`CuspidalInductionCompressionEventuallyStable` tests every actual normalized
induction from an arbitrary cuspidal smooth Levi object in the enlarged
carrier universe. It imposes no irreducibility, admissibility, finite
generation or finite length on that object.

`compressedAction_eventuallyStable_of_leftExact` handles a general left
exact row of actual smooth representations. It converts the two supplied
eventual-stability witnesses to stationary thresholds, chooses a common
larger positive threshold, and applies the same-power left-exact
compression theorem. Compact averaging preserves exactness of the fixed
modules, and the maps commute with the actual compressed actions.

The pointwise theorem first works in the enlarged carrier universe.
The finite embedding target embeds an arbitrary object `E` into an actual
finite sum `B` of normalized inductions of cuspidal objects. Form the actual
smooth quotient `Q = B / image(E)`, and apply the same embedding target
again to embed `Q` into a second actual finite induced-cuspidal sum `C`.
The composite map `B → Q → C` has kernel exactly the image of `E`, because
the second map is injective. Thus `E → B → C` is left exact.

Each of `B` and `C` has eventually stable compression: only finitely many
standard indices occur, so the finite-support direct-sum theorem combines
the supplied pointwise stability of all its summands. The left-exact
theorem then proves eventual stability for `E`. No preservation by an
arbitrary surjective intertwiner is assumed.

For an object in the original carrier universe, its actual `ULift` belongs
to the enlarged universe. The actual equivariant `up` and `down` maps make
the original representation a retract. Compression naturality transfers
the same positive stable power back to the original carrier.

`uniformCompressionStationary_of_cuspidalInduced` applies the published
countable-direct-sum diagonal argument. Its conclusion chooses a single
threshold before every smooth object of carrier universe `uV` and includes
both stationary power chains and their complementarity.

Worker 1751 derives this reduction from the actual finite embedding target,
smooth quotient and direct-sum constructions, compact-average exactness,
compression naturality, stable-power threshold comparison, and carrier
lifting. It is not a proof of either of its representation-theoretic
premises or of the dynamic-parabolic uniform theorem. The geometry and
contraction hypotheses must establish those premises before this reduction
can discharge that theorem.
