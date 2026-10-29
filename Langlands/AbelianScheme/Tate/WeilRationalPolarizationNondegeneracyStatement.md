# Geometric-point nondegeneracy of full and away polarization Weil pairings

`RationalPolarizationWeilNondegeneracyStatement` is an unproved
proposition definition for the existing polarization Weil pairings at a
characteristic-zero geometric point.

The quantified base S is quasi-separated, and A is an actual abelian
scheme over S. The statement retains the chosen relative dual, its
geometry, the inverse Poincare line bundle and evaluation, and all
tensor/Picard propositions used by the published constructors.
The homomorphism `lam` satisfies the actual `IsPolarization` predicate:
it is an isogeny with an ample Mumford presentation on each geometric
fibre after a possible extension of its field. The conclusion is
evaluated at `Over.mk s`, where `s : Spec (CommRingCat.of K) ⟶ S`,
K is algebraically closed and `[CharZero K]`. Characteristic zero is
required at this point; it is not required everywhere on S.

The four conclusions use the actual maps from
`Langlands.AbelianScheme.Tate.WeilRationalAlongHom`:

1. `rationalWeilAlongHomBilinearMap` for the full predicate
   `fun _ => True` is nondegenerate over Q.
2. The same map for `fun n => Nat.Coprime n m` is nondegenerate over Q
   for every natural m.
3. `adelicWeilAlongHomBilinearMap` for the full predicate is
   nondegenerate over `Global.FiniteAdeles ℚ` for every explicit
   `h : Global.RationalProfiniteIntegerAdeleComparison`.
4. `awayAdelicWeilAlongHomBilinearMap` is nondegenerate over
   `Global.PrimeToFiniteAdeles m` for every h, m and coupled comparison
   `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.

In the third conclusion both copies of the input and the output twist
use that same h. In the fourth conclusion
all three modules use the same hAway, whose type also records its
compatibility with h. The comparisons concern scalar rings. They are
not isometries supplied to identify an arbitrary form with the Weil
pairing.

The full rational carrier is
`GroupScheme.Tate.RationalFull A.toGrp (Over.mk s)`, namely
`ℚ ⊗[ℤ] GroupScheme.Tate.Full A.toGrp (Over.mk s)`. The away carrier
is `GroupScheme.Tate.RationalAway A.toGrp (Over.mk s) m`, formed by
the same rationalization of the inverse limit over orders coprime
to m. These are the published limits of actual multiplication-kernel
points. The adelic maps have the same respective carriers, equipped
with their published scalar actions; the statement does not tensor
the integral module over Z with the finite adeles.

The respective outputs are the actual full and away rational
roots-of-unity twists:
`TateTwist.Divisibility.RationalFull Γ(Spec K, ⊤)` and
`TateTwist.Divisibility.RationalAway Γ(Spec K, ⊤) m`.
The maps use beta(lam(y))(x), with pullback in the second variable.
No roots of unity or trivialization of either twist are chosen.

In all four conclusions `LinearMap.Nondegenerate` means that both
radicals vanish. If a vector pairs to zero with every vector in the
other input, it is zero; the assertion holds in each variable.
It does not assert a module equivalence with a dual or integral
perfectness. No arbitrary selected predicate is quantified:
the conclusions concern the full and away systems. The away assertion
includes m = 0 and m = 1. At m = 0 only order 1 is retained and the
Tate module is zero, so the radical assertion still has its usual
meaning. For a prime m this is the prime-to-m case.

`RelativeFiniteWeilTransitionStatement` is an explicit constructor
hypothesis. No finite alternation, prime-adic nondegeneracy, full
nondegeneracy or perfectness proposition is assumed.

The provenance is derived from the following registered original
sources:

- Harris and Taylor, *The Geometry and Cohomology of Some Simple
  Shimura Varieties* (2001), Chapter I, printed p.18 / PDF p.26,
  registered `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  This defines the full and away limits and their rationalization
  over Z. Section III.1, printed p.91 / PDF p.99, uses the full
  adelic polarization Weil pairing in the characteristic-zero PEL
  level condition.
- Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
  draft built 2012-02-08, registered
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
  SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  Chapter X, (10.6)-(10.7), printed p.144 / PDF p.148, gives
  rational prime-adic invertibility of an isogeny away from the
  characteristic. Chapter XI, (11.11), printed pp.162-163 /
  PDF pp.166-167, fixes the pairing convention and distinguishes
  integral perfectness from its polarization pullback. Section
  (11.23), printed p.168 / PDF p.172, constructs the perfect
  unpulled integral Tate pairing into Z_p(1).

These passages provide the field-level ingredients. Over an
algebraically closed field of characteristic zero they give
prime-adic rational nondegeneracy for a polarization at every prime.
Passing to the full and away systems requires the actual prime
coordinate comparisons, compatibility of the constructed pairings
with those coordinates, and enough global vectors to detect each
local radical. The Library's
`GroupScheme.Tate.PrimeComparison.rationalRestrictedProductComparison`
and `rationalAwayRestrictedProductComparison` give exact-coordinate
additive comparisons for the underlying Tate modules. They do not
alone prove the requisite pairing compatibility or nondegeneracy.
The adelic conclusions must also preserve the stated scalar actions.

For a relative abelian scheme evaluated at s the proof further needs
the comparisons of its constructed dual, torsion/Tate modules and
Poincare-derived Weil pairing with those on the geometric fibre.
The field citations do not prove these Library identifications.
All of these steps remain obligations for a separate proof task;
no nondegeneracy theorem is proved here. There is no assertion of
integral perfectness for a nonprincipal polarization or of
nondegeneracy on arbitrary test schemes.
