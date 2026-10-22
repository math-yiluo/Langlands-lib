# Character twists of bundled smooth representations

Author: Worker 23.

This module packages the published scalar twist `Langlands.twist χ ρ`, with
action `(twist χ ρ)(g)(v) = χ(g) • ρ(g)(v)` on the same carrier, as an
operation on the bundled smooth category `Langlands.SmoothRep R G` of
`Category/Basic`. Here `R` is a commutative ring, `G` a group with a topology,
and `χ : G →* Rˣ` a unit-valued character whose kernel is open. No continuity
of the group operations, unitarity of `χ`, or topology or dimension of the
carrier is assumed.

## Constructions

- `equivOfRepresentationEq h` turns an equality `ρ = σ` of actions on one
  carrier into an actual `Representation.Equiv` whose linear part is the
  identity.
- `SmoothRep.twist χ hχ A` is `SmoothRep.of (twist χ A.representation)`, with
  smoothness from the published `isSmooth_twist_iff` (open kernel `hχ`).
  `twist_representation` records that its action is the published twist.
- `SmoothRep.twistFunctor χ hχ` is the endofunctor sending a morphism to the
  same underlying linear map, through the published `twistIntertwining`.
  Identity and composition hold by definition.
- `twistOneIso` identifies the twist by the trivial character with the object,
  and `twistTwistIso` identifies successive twists by `η` then `χ` with the
  twist by `χ * η`. Both are built from the published identities `twist_one`
  and `twist_twist` by `equivOfRepresentationEq` and `SmoothRep.mkIso`. The
  open-kernel proof for `χ * η` is supplied as an argument, since separate
  continuity of multiplication is not assumed.
- `twistIso` is the image of an isomorphism under the functor.
- `SmoothRep.isAdmissible_twist_iff` (Noetherian `R`) restates the published
  `Langlands.isAdmissible_twist_iff` for bundled objects. Over a field `k`,
  `SmoothRep.isIrreducible_twist_iff` restates the published
  `Langlands.isIrreducible_twist_iff`.

## Isomorphism classes

- `SmoothRep.IsoClass.twist χ hχ` descends the twist to the published quotient
  `IsoClass R G` by categorical isomorphism, using `twistIso`.
  `IsoClass.twist_isoClass` is the defining equation, and `IsoClass.twist_one`
  and `IsoClass.twist_twist` are the group-action laws on classes.
- Over a field `k`, `IrreducibleAdmissibleRep.twist` twists an object of the
  published full subcategory of irreducible admissible objects; both conditions
  are transported by the two equivalences above. `twistFunctor` is the
  restricted endofunctor (`ObjectProperty.lift`), and `isoMk` lifts an
  isomorphism of underlying smooth objects to the full subcategory.
- `SmoothDualClass.twist χ hχ` is the induced map on the published smooth dual
  `SmoothDualClass` (classes of irreducible admissible objects), with
  `SmoothDualClass.twist_mk`, `twist_one` and `twist_twist`.

All universes stay as given: an object of `SmoothRep.{uR, uG, uV}` twists to an
object of the same universe, and the class maps preserve their universes.

## Provenance

The twist convention is that of the published `Twist/Definitions` pair: the
scalar realization of tensoring with a one-dimensional representation, as in
Henniart (2000), section 1.2(2), printed page 440, where representations of
the general linear group are twisted by `χ ∘ det` (source
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`). This module
adds no new mathematics beyond that convention: it is an internal packaging of
the published smoothness, admissibility, irreducibility and algebra theorems
of `Twist/{SmoothProof,AdmissibilityProof,SubquotientProof,AlgebraProof}` into
the category and class spaces of `Category/Basic`.

## Not claimed

The module does not identify twists with tensor products by a character
representation, does not relate twists to induction or Jacquet modules, and
does not twist supercuspidal objects. Supercuspidal closure under characters
of the determinant is `Classification/SupercuspidalTwist`.
