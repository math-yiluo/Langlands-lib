# Inertial classes inside a represented standard Levi

Let `D : BernsteinLeviPresentation i ν J j` present a closed connected
reductive representative `j : M ⟶ G` of the standard Levi with label `J`.
`BernsteinInnerInertiaStatement` embeds the inertial classes of the intrinsic
family `D.standardFamily family` into `StandardLeviInertialClass i ν family J`.
On representatives it sends a datum to `D.ambientDatum family a`. The field
and representation-carrier universes are independent. Both point groups have
the canonical topologies, with the local compactness and nonarchimedean group
instances for their Bernstein families. Local finite type supplies the full
unramified twists on each inducing Levi.

The intrinsic root label `K` becomes the ambient label
`leviIndex J (D.innerIndex family K)`, a subset of `J`. The representation
is pulled back along the inverse of `D.innerLeviIso family K`. Pullback
preserves irreducibility and transports represented supercuspidality. The
latter gives the standard Jacquet vanishing tests through
`isCuspidal_of_all_represented_parabolics_of_standardCocharacter` and
`rationalLeviCuspidalityTransport`.

An intrinsic conjugating point maps to a point of the literal standard Levi
of label `J`. In the reverse direction a point of that subgroup lifts through
`D.points`. The compatibility of `innerIso` with `j` and the commutative
inclusion triangles for `innerLeviIso` give the two algebraic conjugacies.
The square of inducing Levi isomorphisms yields a smooth object isomorphism
by composition of pullbacks. `conjugatePullback_iff` uses this square for
arbitrary smooth inducing objects. For cuspidal data, `inertiaRelated_iff`
uses the same comparison with full unramified twists. Pullback by the inverse
isomorphism and cancellation of successive inverse pullbacks reflect both
relations. The quotient lift is well-defined by preservation of inertia and
injective by reflection.

The construction uses the description of standard parabolics inside a Levi
in David Renard, *Représentations des groupes réductifs p-adiques*, French
edition of 9 July 2026, V.3.10–V.3.11 (printed p. 112, PDF p. 118), and the
inertial relation of VI.7.1 (printed pp. 180–181, PDF pp. 186–187). The
registered source is `renard-2026-representations-groupes-reductifs-padiques`
with SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
