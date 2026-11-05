# Apartment class rigidity from actual opposite factor pairs

This internal assembly implements the final identification in the proof of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 6.2.6,
printed p.216 (PDF p.247). It uses the actual normalizer-equivariant affine
comparison and its preservation of valuation values at nonidentity root
points with supplied opposite factor pairs. The registered 2024 corrections,
Chapter 4 pp.28–29 and Chapter 6 p.32, do not change this argument.

The module retains `RelativeRoot.HasOppositeFactorPairs i` as an explicit
premise. It proves neither this geometric existence predicate nor the exact
unconditional `OmegaCompatibleApartmentUniquenessStatement`.

`OmegaCompatibleApartmentRigidityStatement.{u}` is the Prop-valued statement
of this conditional result. It quantifies over every local field in universe
`u`, an affine connected reductive group, an actual maximal split torus with
its monomorphism witness, opposite-factor-pair existence, a common actual
centralizer datum, and two full omega-compatible apartment classes. Its
conclusion is equality of those classes. The final helper theorem
`omegaCompatibleApartmentRigidity` proves this statement by applying the
class-rigidity lemmas below. This additional statement records the scope of
the intermediate result; the published unconditional target and all its
imported pairs are unchanged.

`IsRootDatumValuation.eq_of_eq_on_nonidentity_root_points` is an internal
extensionality lemma for the Library's extended root-function families over
an arbitrary field in universe `u`. Agreement on nonidentity points of each
actual relative root group determines the entire family. The Library's
`eq_top_of_not_mem_roots` and `eq_top_of_not_mem` fields set the value to
infinity on nonroots and outside the corresponding root group. These fields
implement the Library's extension of KP's root-group functions to all
characters and rational points. V 1's `eq_top_iff` gives infinity at the
identity. The proof splits into precisely these cases. KP's V 0 is the
separate three-values condition (`three_le_encard`, Definition 6.1.2, printed
p.199/PDF p.230); this extensionality argument does not use it.

The remaining lemmas compare two full omega-compatible `KPApartmentData`
over a nonarchimedean local field in arbitrary universe `u`, at an actual
maximal split torus of an affine connected reductive group, with a common
actual centralizer datum. Compatibility is on all rational points of that
centralizer.

`KPApartmentData.val_eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs`
assumes an affine equivalence between the two apartments, with identity
derivative and equivariance for their original normalizer actions. At each
nonidentity root point, it chooses an actual opposite factor pair and applies
the imported value-preservation lemma. Extensionality then proves equality
of the full original root-function families at corresponding apartment
points.

`KPApartmentData.eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs`
chooses a point in the nonempty first apartment. Its family agrees with its
image family's value, so belongs to both carriers. The published
`KPApartmentData.eq_of_common_mem` identifies the full equipollence classes.

`KPApartmentData.eq_of_isOmegaCompatible_of_hasOppositeFactorPairs`
supplies the affine equivalence constructed by the imported finite relative
Weyl quotient averaging argument, its identity derivative and its actual
normalizer equivariance. Thus actual opposite-pair existence is the only
additional premise beyond the fixed data of the unconditional target.
No V 7, AS 5 or Tits-system premise is introduced.
