# The actual projective system of corner centers

This definition unit implements the corner-center construction in David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.1.7, printed page 13 / PDF page 19. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The cited page was read in full, together with the opening of I.1.7 on
PDF page 18 and the I.1.1–I.1.2 order and corner definitions on PDF
pages 12–13.

## Source correspondence

In the theorem of I.1.7, Renard identifies the center of `M(A)` with the
center of the completion and with the projective limit over
`ℐ = Idem(A)` of the centers of the rings `eAe`. Its proof considers the
transition maps `fAf → eAe`, `a ↦ eae`, for `e ≤ f`, and shows that they
induce transition maps between the centers: a central `z` of `fAf`
commutes with `e`, and for `x ∈ eAe` one has
`[eze, x] = ezx − xze = zex − xez = zx − xz = 0`. The source says that
this defines the projective system whose limit is to be identified.
This module constructs exactly that projective system, its limit as a ring
of coherent families, and the categorical limit cone. It does not prove
any of the identifications in the theorem.

Renard's order on `ℐ` (I.1.1) is inclusion of corners, so `e ≤ f` means
`eAe ⊆ fAf`, and then `e = ef = fe`. The source's `ℐ` is directed when `A` is idempotented (the
lemma of I.1.2), but the system and its limit here require neither
directedness nor an idempotented hypothesis.

The registered 2010 errata
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
were read on their first PDF page, which covers 2010 printed pages 3–23.
None of those corrections concerns the transition maps `a ↦ eae` or the
centrality computation. The errata cite pages of the 2010 printing, which
differ from the 2026 edition. The public notes record no other Renard
errata for I.1.7.

Worker 6 wrote the Lean/Markdown pair. Worker 734 audited it against the
published ring core and the source, added the further interfaces and
checks listed below, and revised this Markdown.

## Corner centers and original operations

The ambient ring keeps its original `NonUnitalRing` operations. It is not
assumed commutative, unital, nontrivial or idempotented. The module uses
the published `Idempotent A`, its corner order, and the published
unital corner `Idempotent.Corner e` with its named ring `Corner.ring`,
whose identity is `e`. `Idempotent.CornerCenter e` is the actual subtype
of `Subring.center (Idempotent.Corner e)`, and `CornerCenter.commRing` is
the commutative ring inherited from Mathlib's center subring.
`toCorner` is the unital subring inclusion. `toAmbient` composes it with
the published nonunital corner inclusion; it is only nonunital because
`A` need not have an identity. `toCorner_apply`, `toAmbient_apply` and
`toAmbient_function` show that these maps take the subtype values, and
`toAmbient_one` shows that the unit goes to `e`. Injectivity of
`toAmbient` comes from the two subtype inclusions. `ambient_commute`
restates centrality in the corner through the ambient multiplication.

## Transitions

For `e ≤ f`, `sandwich` sends a central element `z` of `fAf` to the
corner element `e*z*e` of `eAe`. Corner membership uses the published
`mem_corner_iff_exists`, which describes corner elements as sandwiches.
The included `e`, `Corner.inclusion h 1`, lies in `fAf`, so `z` commutes
with it (`ambient_commute_idempotent`). With idempotence this gives
`e*z*e = e*z` (`sandwich_ambient_eq_left`). For `a` in `eAe`,
`sandwich_mem_center` uses `e*a = a = a*e`, associativity and the
commutation of `z` with the included `a` to prove that `e*z` commutes
with `a`. This follows the source computation.

`transition h` bundles the result as a unital ring homomorphism
`CornerCenter f →+* CornerCenter e`. Distributivity gives the zero and
addition laws. The unit law uses `e*f*e = e`, from the published
`le_iff_mul` and idempotence. For multiplication,
`e*(z*w) = (e*z*e)*w = (e*z)*(e*w)`, using `e*z*e = e*z` and
associativity. These proofs use the centrality of `z`. They do not claim
that sandwiching is multiplicative on all of `fAf`, which can fail.

The interfaces are exact. `transition_ambient` gives the ambient value
`e*z*e` at a point, and `transition_ambient_function` gives the whole
composed ambient function. `toCorner_transition` and
`toCorner_transition_function` say that the corner-valued map is
`sandwich h`. `transition_refl` and `transition_comp` are equalities of
whole ring homomorphisms. The first uses corner membership `e*z*e = z`.
The second uses `e*f = e = f*e` and associativity.

## The coherent-family ring

`IdempotentedRingCornerCenter.coherentSubring A` is the actual subring of
the dependent product `∀ e, CornerCenter e`. Its carrier is the set of
families `x` with `transition h (x f) = x e` for every `h : e ≤ f`, as
`mem_coherentSubring` states. The homomorphism laws of the transitions
prove closure under zero, one, addition, negation and multiplication.
`Family A` is exactly the subtype of this subring, and `Family.commRing`
is its inherited commutative ring. No other ring structure is put on the
families.

`Family.coordinate e` is the coordinate ring homomorphism. By
`coordinate_eq_eval_comp_subtype` it equals Mathlib's
`Pi.evalRingHom` at `e` composed with the subring inclusion.
`ambientCoordinate e` composes the coordinate with the nonunital ambient
inclusion. Their application and whole-function lemmas give the nested
subtype values. `coordinate_transition` states coherence as an equality
of whole ring homomorphisms. The ambient form is
`ambientCoordinate_compatible` at a point, and
`ambientCoordinate_compatible_function` as an equality of whole functions
after composing with `a ↦ e*a*e`. That function on `A` is not claimed to
be a ring homomorphism.

## Universal property

Let `R` be a ring in an independent universe, possibly noncommutative,
and let `p e : R →+* CornerCenter e` satisfy
`(transition h).comp (p f) = p e` as whole maps. `Family.lift` sends `r`
to the family `e ↦ p e r`. Membership follows by evaluating the
coherence equalities at `r`, and the ring laws hold coordinatewise.
`coordinate_lift` is the projection identity as an equality of ring
homomorphisms, and `lift_coordinates_function` gives the whole underlying
dependent function. `lift_unique` evaluates the given coordinate
identities at each `r` and coordinate, then uses family and ring
homomorphism extensionality.

## Diagram, cone and limit

`diagram A` is a functor from the opposite of the published idempotent
preorder to `CommRingCat`. It sends `e` to its corner center
(`diagram_obj`) and an arrow from `h : e ≤ f` to `transition h`
(`diagram_map_hom`). `transition_refl` and `transition_comp` prove the
functor laws. `cone A` has vertex `CommRingCat.of (Family A)` (`cone_pt`)
and the coordinates as legs (`cone_π_app_hom`). Naturality is
`coordinate_transition`.

`coneIsLimit A` is a direct `IsLimit` construction.
`cone_legs_compatible` turns the naturality of any cone `s` into the
whole-map compatibility of its legs, using `homOfLE`. The lift is
`Family.lift` of the legs (`coneIsLimit_lift_hom`), and factorization
holds by definition. Uniqueness evaluates the factorization identities at
each ring element and coordinate. All bundled objects use the named
inherited rings.

## Universes

The corner centers and the family carrier live in `Type uA`, and the
diagram takes values in `CommRingCat.{uA}`. The universe `uR` of the
universal source is independent of `uA` and does not enlarge the family
carrier. The limit applies `Family.lift` with `R` the cone vertex, so in
universe `uA`.

## Checks

The module checks, as complete unapplied terms, the constructors,
inclusions, transitions, whole-map and coherence identities, membership,
the coordinate as evaluation, the universal lift with its identities, and
the diagram, cone, leg compatibility, limit and lift formula. The checks
are done at arbitrary `uA, uR` and again at `(uA, uR) = (0, 1)` and
`(1, 0)`.

Further checks select the original ambient ring when a second
`NonUnitalRing` instance on `A` is present. Others select the named
corner, center and family rings when competing ring instances on
`Corner e`, `CornerCenter e`, `CornerCenter f` and `Family A` are
present. They check the diagram objects and cone vertex against these
structures, the coordinate multiplication law and the universal lift.
The overlapping-instance linter is turned off only in the section that
installs two ambient instances on purpose.

For the zero idempotent, the checks show that the center is a
subsingleton, that it lies below every idempotent, and that center
inclusions, transitions into it and family coordinates at it have ambient
value zero. For a subsingleton ambient ring, injectivity and family
extensionality show that each center and the family ring are
subsingletons, that the family unit equals zero and that lifted elements
vanish; the limit construction still applies. No nontriviality
assumption is made.

## Provenance and scope

The source supplies the corner-center transitions and the projective-limit
description. The subring and subtype, the bundled ring maps, the
independent-universe universal lift, the categorical diagram, cone and
limit, and the explicit interfaces are internal packaging, with the
intrinsic proofs described above. This unit does not identify the
families with the categorical center of nondegenerate modules, the
commutant of `A` in its completion, or the center of the completed ring.
The unital comparison and the I.1.8 scalar evaluation are also left to
separate successors. Compilation is not independent acceptance or
publication.
