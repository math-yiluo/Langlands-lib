# A genuine special reference apartment

This module is an internal composition of the special-torus existence theorem,
rational conjugacy, full valuation transport and canonical coefficient
comparison. It constructs a reference apartment containing a maximal split
torus over the original field and transfers a prescribed fixed quotient point to
that reference building. It is a supporting construction for the fixed-point
split-torus problem, rather than a separate translation of a literature result.

## Precise meaning

Let `F` be any nonarchimedean local field, let `K` be its actual maximal
unramified extension `inertiaFixedField F`, and let `v` be
`MaximalUnramified.valuation F`. All fields and schemes are in the arbitrary
universe `u`; no characteristic restriction is imposed. Let `G` be a connected
reductive group over `F`, and let `iT : T.toGrp ⟶ G` be a descended commutative
group embedding whose scalar extension is a maximal split torus of `G_K`.
Retain the supplied valuation apartment `D`, actual centralizer datum `C`,
full integer-valued V6 compatibility, canonical coefficient stability `hD`,
and a prescribed point `y` of `D.ReducedBuilding` fixed by that coefficient
action.

`UnramifiedSpecialReferenceApartmentStatement` asserts that there are a
commutative group scheme `S` and an actual embedding `iS : S.toGrp ⟶ G`
which is a maximal split torus over `F`, together with
`SpecialReferenceRealization F G T iT D y S iS`.
The latter proposition records:

* a commutative group scheme `T'` over `F`, an actual closed embedding
  `j : T'.toGrp ⟶ G`, and a map `f : S ⟶ T'` satisfying
  `groupHom f ≫ j = iS`;
* maximal splitness of the actual scalar extension `j_K`;
* a valuation apartment `E` for `j_K` and an actual centralizer datum `C'`
  satisfying full integer-valued V6 on the entire valuation class;
* canonical coefficient stability `hE`, a point `q` of `E.ReducedBuilding`
  fixed by its canonical coefficient action, and an equivalence
  `r : E.ReducedBuilding ≃ D.ReducedBuilding` satisfying `r q = y`;
* the identity `r (g • z) = g • r z` for every original ambient rational
  point `g : G_K(K)` and every `z` in the new quotient.

In particular, the comparison retains the same full ambient group action.
The new point is a fixed point of the actual new reduced-building quotient.
No apartment representative for `y` or `q` is asserted. The original descended
torus need not contain a maximal split torus over `F`.

## Implemented construction

`KPApartmentData.specialReferenceRealization` first works with a prescribed
maximal split torus `iS` over `F`. The imported theorem `specialTorusExistence`
from `SpecialTorusExistenceProof` gives `T'`, `j`, the factorization `f`,
closedness of `j`, and maximal splitness of `j_K`.

The published `connectedReductiveFieldExtensionStatement` gives connected
reductivity of the actual `G_K`. Its smoothness, affineness and connectedness
allow `smoothMaximalSplitTorusConjugacy` to compare the original torus and
`j_K`. It returns an actual point `g : G_K(K)` and an isomorphism of the
underlying group schemes. `CommGroupScheme.isoOfGroupIso` gives the corresponding
commutative-group isomorphism `e`, with the same equation
`iT_K ≫ innerIso(g).hom = groupHom e.hom ≫ j_K`.

The apartment `E` is exactly
`D.transport e (GroupScheme.innerIso G_K g) he`. The centralizer `C'` is
`C.basedTransport e (GroupScheme.innerIso G_K g) he`.
`IntegerValuation.IsOmegaCompatible.transport_basedIso` transports full V6
to these actual data. These inputs are provided by
`IntegerValuationBuildingBasedTransport` and its imported
`FullValidity.DatumTransport.Base`; no torus-only substitute for the full
centralizer equation is used.

`ConjugateApartmentGaloisComparison` supplies
`KPApartmentData.galoisStable_transport_inner`, which derives coefficient
stability of this `E` from `hD`.
Its `exists_galoisFixed_conjugate_preimage` then constructs `q` fixed by the
canonical action on `E`, with image exactly `y`.
The chosen `r` is the actual `D.conjugateReducedBuildingEquiv e g he`.
The published `conjugateReducedBuildingEquiv_smul` proves the displayed
identity for every element of the same original full rational-point group.

Finally, `unramifiedSpecialReferenceApartment` chooses an actual maximal
split torus over `F` using `exists_maximalSplitTorus` from
`MinimalPseudoParabolicConjugacyAssembly` and applies the preceding construction.
Affineness and local finite type are supplied by `hG` and its smoothness.
The choice does not change the prescribed point or the original valuation datum.

## Scope

The construction has no additional model, reference apartment, transporter,
fixed-point or residue premise. All such objects in its conclusion are
constructed from the original data. Its transitive project imports contain none
of the four barred building-descent statements named in the host task.

This module does not construct a reference chamber, an integral split source,
or a residue quotient. Nor does it yet produce a maximal split torus whose
unit subgroup fixes `y`. Those are further obligations of
`UnramifiedFixedPointSplitTorusStatement`. The present result supplies the
special reference data and the fixed-point comparison needed for that argument.
