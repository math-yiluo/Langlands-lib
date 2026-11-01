# The completed-ring centre and its corner-centre comparison maps

Authors: Worker 734.

Module `Langlands.Algebra.IdempotentedRingCenterComparison`. It imports
only the published `Langlands.Algebra.IdempotentedRingRightLimitRing`
(the ring `IdempotentedRingRightLimit.ring hA` on right-compatible
families) and `Langlands.Algebra.IdempotentedRingCornerCenter` (the corner
centres `Idempotent.CornerCenter e` and their coherent-family ring
`IdempotentedRingCornerCenter.Family A`). No imported file is changed.

## Source correspondence

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Pages read: the conventions and I.1.1–I.1.3, printed pp.5–9/PDF11–15
(nonunital conventions, the corner order `e ≤ f` iff `eAe ⊂ fAf`, the
I.1.2 definition `aᵢ = e aᵢ e` for finite families, compatible families,
the product and the unit), and I.1.7, printed pp.12–13/PDF18–19.

The Théorème of I.1.7 (PDF19) says that the centre of `M(A)` is the
centre of the completion `Ā` and is the projective limit over
`ℐ = Idem(A)` of the centres of the rings `eAe`. Its proof contains two
comparison steps used here:

* "Si `ā ∈ Ā` est central, alors il est clair que pour tout `e ∈ ℐ`,
  `e ā e = ā(e)` est dans le centre de `eAe`." This is the forward map
  `Center.coordinate` and its bundle `Center.toFamily`.
* For the converse the source shows `e ā = ā e` for every `e`, using a
  larger `f ≥ e` and the centrality of `ā(f) = f ā f` in `fAf`, and then
  concludes that `ā` commutes with `A` because `A` is the union of the
  `eAe`. This is the reverse map `Family.toRightLimit`, `Family.toCenter`.

The supplementary registered `renard-2010-corrections-complements`
(SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
was read on PDF1. Its early Chapter I corrections concern other
passages and do not change the I.1.7 argument. The 2026 original
governs.

In the published model a compatible right family `x` has coordinates
`x.val e ∈ A e` with `x(f) e = x(e)` for `e ≤ f`; the source's `ā(e)` is
`x.val e`. The source's centre of `Ā` is realised as the actual
`Subring.center` of the published ring `IdempotentedRingRightLimit.ring hA`.

## The actual centre

Throughout, `A : Type uA` carries its original `NonUnitalRing A` and
`hA : IsIdempotented A`. No unit, commutativity, nontriviality, size,
topology or closure hypothesis is used.

* `IdempotentedRingRightLimit.centerSubring hA` is, by definition,
  `Subring.center (IdempotentedRingRightLimit A)` for the ring
  `ring hA`. `centerSubring_eq` states this equality and
  `coe_centerSubring` gives the carrier `Set.center`.
* `mem_centerSubring_iff_mul` is Mathlib's `Subring.mem_center_iff` for
  `ring hA`: `z` is central iff `y * z = z * y` for every compatible right
  family `y`. `mem_centerSubring_iff` restates it with the published
  product: `product hA y z = product hA z y` for every `y`.
* `IdempotentedRingRightLimit.Center hA` is the subtype
  `↥(centerSubring hA)` (`Center.carrier_eq`). Its commutative ring
  `Center.commRing hA` is Mathlib's inherited ring on `Subring.center`
  of `ring hA`. `Center.mul_val`, `Center.one_val` and `Center.add_val`
  record that multiplication, unit and addition are the published
  `product hA`, `unit` (`e ↦ e`) and the original pointwise addition.
* `Center.inclusion hA : Center hA →+* IdempotentedRingRightLimit A` is
  the unital subring inclusion `(Subring.center _).subtype`. Its value is
  `z.val` (`inclusion_apply`), its function is `Subtype.val`
  (`inclusion_function`) and it is injective (`inclusion_injective`).
  `Center.ext` reduces equality to equality of all coordinates
  `z.val.val e`.

## Centre to corner centres

Let `z : Center hA` and `e : Idempotent A`.

* `Center.product_comm` is the membership condition for `z`.
* `Center.left_support`: `e * z(e) = z(e)`. Compare the `e` coordinates
  of `product hA (canonical e) z` and `product hA z (canonical e)`. The
  published `canonical_applyOriginal` gives `e * z(e)` on the left, and
  `e * e = e` with `applyOriginal_idempotent` gives `z(e)` on the right.
* `Center.coordinate_mem_corner`: `z(e) ∈ eAe`, from left support and
  the published right support `z(e) * e = z(e)`.
* `Center.commute_corner`: for `a ∈ eAe`, `a * z(e) = z(e) * a`. Compare
  the `e` coordinates of `product hA (canonical a) z` and
  `product hA z (canonical a)`. They are `a * z(e)` and
  `applyOriginal hA z (a * e)`. Since `a * e = a` and `e * a = a`,
  `applyOriginal_eq` evaluates the latter as `z(e) * a`.
* `Center.cornerCoordinate hA z e : Corner e` is `⟨z(e), _⟩`, with
  ambient value `z(e)` (`cornerCoordinate_ambient`).
  `cornerCoordinate_mem_center` puts it in `Subring.center (Corner e)`
  by `commute_corner` and injectivity of `Corner.toAmbient`.
* `Center.coordinate hA e : Center hA →+* CornerCenter e` sends `z` to
  `⟨cornerCoordinate hA z e, _⟩`, the source's `e z e = z(e)`. Zero, one
  and addition are definitional: the unit family has coordinate `e`,
  which is the unit of `Corner e`. For multiplication, the published
  `product_val` with `f = e` and the left support `e * w(e) = w(e)` give
  `(z * w)(e) = z(e) * w(e)`, the corner product.
* Formulas: `coordinate_ambient` (ambient value `z.val.val e`),
  `toCorner_coordinate`, the whole functions `coordinate_function` and
  `coordinate_ambient_function`, and `coordinate_ambient_sandwich`
  (ambient value `e * z(e) * e`).
* `Center.transition_comp_coordinate`: for `h : e ≤ f`,
  `(CornerCenter.transition h).comp (coordinate hA f) = coordinate hA e`
  as bundled ring maps. The ambient value of the left side is
  `e * z(f) * e`. Right compatibility `z(f) * e = z(e)` turns it into
  `e * z(e)`, and left support turns that into `z(e)`.
* `Center.toFamily hA : Center hA →+* Family A` is the published
  `Family.lift` of these coordinates, so its ring structure is exactly
  `Family.commRing`. Formulas: `coordinate_comp_toFamily`
  (`(Family.coordinate e).comp (toFamily hA) = coordinate hA e`),
  `toFamily_val`, the whole dependent function `toFamily_function`
  (`Subtype.val ∘ toFamily hA = fun z e => coordinate hA e z`), and
  `ambientCoordinate_comp_toFamily` / `ambientCoordinate_toFamily_function`
  for the composite with `Family.ambientCoordinate e`. Here
  `Center.ambientCoordinate hA e : Center hA →ₙ+* A` is
  `CornerCenter.toAmbient e` after `coordinate hA e`, with value
  `z.val.val e` (`ambientCoordinate_apply`, `ambientCoordinate_function`).

## Corner centres to the centre

Let `x : Family A`, a coherent family of corner-central elements.

* `Family.ambientCoordinate_left_support` and `_right_support`:
  `e * x(e) = x(e)` and `x(e) * e = x(e)`, from corner membership
  (`mem_corner_iff`) of `(x.val e).val`.
* `Family.ambientCoordinate_mul_of_le`: for `h : e ≤ f`,
  `x(f) * e = x(e)`. Centrality in `fAf` makes `x(f)` commute with `e`
  (`CornerCenter.ambient_commute_idempotent`). The published
  `sandwich_ambient_eq_left` rewrites `e * x(f)` as `e * x(f) * e`, and
  sandwich coherence (`ambientCoordinate_compatible`) identifies this with
  `x(e)`. Right support and right compatibility are derived, not assumed.
* `Family.toRightLimit x : IdempotentedRingRightLimit A` is the family
  `e ↦ (x.val e).val.val`. `toRightLimit_val` and
  `toRightLimit_function` give its coordinates.
* `Family.toRightLimit_mul hA`:
  `toRightLimit (x * y) = product hA (toRightLimit x) (toRightLimit y)`,
  by `product_val` at `f = e` and left support of `y(e)`.
* `Family.product_toRightLimit_comm hA x y`: for every compatible right
  family `y`, `product hA y (toRightLimit x) = product hA (toRightLimit x) y`.
  This is the implemented route; see the next section.
* `Family.toRightLimit_mem_centerSubring` places `toRightLimit x` in
  `centerSubring hA`.
* `Family.toRightLimitRingHom hA : Family A →+* IdempotentedRingRightLimit A`
  (for `ring hA`) bundles `toRightLimit`. Zero, one and addition are
  definitional, and multiplicativity is `toRightLimit_mul`. Formulas:
  `toRightLimitRingHom_apply`, `toRightLimitRingHom_function`.
* `Family.toCenter hA : Family A →+* Center hA`, from `Family.commRing`
  to `Center.commRing hA`, sends `x` to `⟨toRightLimit x, _⟩`.
  Formulas: `toCenter_val`, the pointwise coordinate formula
  `toCenter_coordinate` (`(toCenter hA x).val.val e = (x.val e).val.val`),
  the whole coordinate function `toCenter_function`, and the identities
  after the centre inclusion: `inclusion_toCenter`, the function
  identity `inclusion_comp_toCenter_function`, and the ring-map
  identity `inclusion_comp_toCenter`
  (`(Center.inclusion hA).comp (toCenter hA) = toRightLimitRingHom hA`).

## Implemented centrality route

The source proves the converse through `e ā = ā e` and the union of the
corners. The Lean proof uses a direct finite-local-unit argument, which
the task contract permits. Fix `y` and `e`. Using
`IsIdempotented.iff_two_sided_local_units` (the I.1.2 definition),
choose an idempotent `f` with `f * a = a = a * f` for `a ∈ {e, y(e)}`. Then `e ≤ f` (`le_iff_mul`)
and `y(e) ∈ fAf`. By `product_val`, the `e` coordinates are
`y(e) * x(e)` (left support of `x(e)` by `e`) and `x(f) * y(e)`
(`f * y(e) = y(e)`). Then

`y(e) x(e) = y(e) (x(f) e) = y(e) (e x(f)) = (y(e) e) x(f) = y(e) x(f) = x(f) y(e)`,

using right compatibility, centrality of `x(f)` against `e`, the
published right support `y(e) e = y(e)`, and centrality of `x(f)` in
`fAf` against `y(e)` (`CornerCenter.ambient_commute`). No continuity,
density, topology or closure argument is used.

## Universes

Everything lives at the single universe `uA` of `A`. `Center hA` and
`Family A` are in `Type uA`.

## Checks in the module

* Complete unapplied interfaces of every declaration above, from
  `centerSubring` to `inclusion_comp_toCenter`, with their full binder
  telescopes. This includes the named ring `Center.commRing`, the
  inclusion, both comparison maps and all whole-map and coordinate
  identities. The checks are made at arbitrary `uA` and separately at
  `Type 0` and `Type 1`.
* `CompetingAmbient`: with two `NonUnitalRing A` instances, the centre,
  its type, left support, coordinates, `toFamily`, ambient coordinates,
  `toRightLimit` and `toCenter` are taken at the explicitly selected
  original instance.
* `CompetingStructures`: with competing `Ring (IdempotentedRingRightLimit A)`,
  `CommRing (Center hA)`, `Ring (Corner e)`, `CommRing (CornerCenter e)`
  and `CommRing (Family A)` instances present, the membership test,
  inclusion, the centre's multiplication (`product hA`), addition and
  unit (coordinate `e`), multiplicativity of `coordinate`, `toFamily`,
  `toRightLimit` and `toCenter`, and `toCenter 1 = 1` are checked with
  the named `ring hA`, `Center.commRing hA`, `Corner.ring e`,
  `CornerCenter.commRing e` and `Family.commRing A`.
* `ZeroRings`: the coordinate of any central family at the zero
  idempotent is `0`; for the zero ring `PUnit` (with
  `IsIdempotented.of_ring`) the centre is a subsingleton, and both
  comparison maps are instantiated.

`Family.toCenter` was inspected: its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance and scope

Source content: the centre of the completion, the coordinates
`e ā e = ā(e)` of a central element as central elements of `eAe`, and
the converse construction from a coherent family of corner-central
elements (Renard I.1.7, PDF19). Internal faithful packaging: the
realisation as Mathlib's `Subring.center` of the published ring and its
subtype, the bundled unital ring maps and the whole-function formulas.
The finite-local-unit centrality proof is an internal route that
replaces the source's union-of-corners argument. Its algebraic content
is the same, and it is used because it needs no topology. All ring-map
laws and membership facts are proved from the original operations and
the published local-unit, product and family lemmas.

Not included: the identities saying the two maps are mutually inverse,
the resulting ring equivalence and the final comparison theorem.
Identification of the centre with the commutant of the image of `A` and
with the categorical centre of nondegenerate modules is also not
included. Neither are topology and closure, the unital specialisation
and I.1.8. These are separate successor obligations.
