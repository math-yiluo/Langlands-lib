# Scheme points along a closed subscheme and its complement: proof

`Langlands.AlgebraicGeometry.PointTopology.schemePointStratification` proves
`SchemePointStratificationStatement` from `SchemePointStratificationStatement`, in its
universe `u` and its full generality: an arbitrary commutative ring `R`, an arbitrary
commutative `R`-algebra `S`, arbitrary `R`-schemes `X` and `Z` with a closed immersion
`i : Z ⟶ X` over `Spec R`, and an arbitrary actual point `p : Spec S ⟶ X` over `Spec R`.
No affineness, finiteness or reducedness hypothesis is added. The statement records the
support and factorization distinction in Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed p. 5, Remark 3.3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Throughout, `J` is the pullback `i.left.ker.comap p.left` of the ideal sheaf of `Z` to
`Spec S`, and `U` is the open complement of the support of `i.left.ker`. The proof works
with Mathlib's ideal sheaves (`Scheme.IdealSheafData`) and with the Library's actual points
`RingPoint R X S` and open-subscheme points from `PointTopology.SchemePoints`.

## The closed and open strata as sets

Mathlib's `Scheme.Hom.support_ker` says that the support of the kernel of `i.left` is the
closure of its image. A closed immersion is a closed embedding, so this closure is the image
itself. Hence the support of `i.left.ker` is `Set.range i.left`, and `U` is the complement of
`Set.range i.left`.

## Clause 1: support

`Scheme.IdealSheafData.support_comap` identifies the support of `J` with the preimage under
`p.left` of the support of `i.left.ker`, that is of `Set.range i.left`. The image of `p.left`
lies in `Set.range i.left` exactly when that preimage is everything, that is when the whole
space `Spec S` lies in the support of `J`. The support–vanishing-ideal Galois connection
(`Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal`) turns this into `J` lying below the
vanishing ideal of the whole space, and `Scheme.IdealSheafData.vanishingIdeal_top` identifies
that vanishing ideal with the nilradical of `Spec S`.

## Clause 2: factorization through the closed subscheme

By `Scheme.IdealSheafData.le_map_iff_comap_le` (pullback of ideal sheaves is left adjoint to
pushforward) and `Scheme.IdealSheafData.map_bot` (the pushforward of the zero ideal sheaf is
the kernel), `J = ⊥` is equivalent to `i.left.ker ≤ p.left.ker`.

- If `p = z ≫ i`, then `Scheme.Hom.le_ker_comp` gives `i.left.ker ≤ (z.left ≫ i.left).ker`.
- Conversely, Mathlib's universal property of closed immersions, `IsClosedImmersion.lift`
  with `IsClosedImmersion.lift_fac`, gives a morphism of schemes `z : Spec S ⟶ Z` with
  `z ≫ i.left = p.left`. It is a morphism over `Spec R` because `i` and `p` are, so it is an
  actual point of `Z`, and `RingPoint.ext` shows that its composite with `i` is `p`.

## Clause 3: factorization through the open complement

By the description of `U` above, this clause asks that the points of the open subscheme
`openOver R X U` map onto exactly the points of `X` whose image lies in `U`. A point of the
open subscheme maps to such a point by the Library's equivalence `openPointEquiv`.
Conversely, `openPointLift` factors a point with image in `U` through `U`, and
`openPointMap_lift` shows that this factorization recovers the point.

## Coverage when the prime spectrum is a single point

An auxiliary step proves, when `PrimeSpectrum S` is nonempty and has at most one element,
that the image of `p` lies in `Set.range i.left` or `p` factors through `U`. The image of `p`
is the image of the unique prime `s` of `S`. If `p.left s` lies in `Set.range i.left`, the
first alternative holds. Otherwise the whole image lies in the complement, and clause 3 gives
the factorization through `U`.

## Clauses 4–6

- Disjointness for nonzero `S`. A nonzero ring has a prime `s`. A factorization `p = z ≫ i`
  puts `p.left s` in `Set.range i.left`, while a factorization through `U` puts it in the
  complement, by clause 3.
- Local Artinian `S`. An Artinian ring has Krull dimension zero, so Mathlib's instance
  `PrimeSpectrum.unique_of_ringKrullDimLE_zero` makes the prime spectrum of a local Artinian
  ring a single point, and the auxiliary step applies.
- Field `S`. A field is a local Artinian ring, so the auxiliary step applies. In its first
  alternative, clause 1 gives `J` below the nilradical of `Spec S`. That nilradical is zero
  because `Spec S` is reduced (`Scheme.nilradical_eq_bot`), so `J = ⊥` and clause 2 gives
  factorization through `Z`.

The local Artinian clause concludes only containment of the underlying image in `Z`, as the
statement does. The module `AffineLineStratificationProof` proves
`ConradRemark33Correction`: for every field `K`, the point of the affine line over the dual
numbers `K[ε]` with coordinate `ε` has image in the origin but factors through neither the
origin nor the punctured line.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
