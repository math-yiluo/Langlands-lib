# Residue data for a coefficient-stable ordinary chamber

This internal supporting composition converts an ordinary regular apartment
facet, stable under the actual coefficient action, into an original maximal
Galois facet and an actual recovered residue quotient with no proper rational
parabolics. It works at arbitrary universe `u` and in both characteristics.

## Scope and exact objects

Retain a descended torus map `i`, its maximal split scalar extension, the
supplied integer-valued apartment `D`, its original coefficient stability,
the actual centralizer `C`, and full `IsOmegaCompatible` datum. The extended
group is connected reductive. No replacement apartment or coefficient action
is introduced.

The general helper
`exists_maximalGaloisFacet_of_regular_stable_apartmentFacet` applies to an
arbitrary field extension with an order-one valuation unit. It takes an
ordinary regular apartment point `x` and invariance of its whole sign facet
under every actual coefficient affine automorphism. It constructs an
original `GaloisFacet E`, with the literal underlying subset

`E.val.val = D.apartmentMap '' AffineRootSystem.facet D.affineRoots x`,

and proves that `E` is maximal for the original full-facet incidence relation.
Regularity concerns the ordinary affine roots of `D`. Stability is imposed
on the whole open facet; the representative `x` need not itself be fixed.

`UnramifiedStableChamberResidueStatement` specializes to the actual maximal
unramified extension of a nonarchimedean local field `F`. It additionally
retains geometric connectedness of the original group for model descent.
For any supplied regular stable facet it returns that same maximal `E`,
actual downstairs relative component models `N0`, an actual recovery of the
published constructed upstairs model at `E.val`, and valid reductive quotient
data `Q0` for `N0`. Every rational parabolic inclusion into `Q0.quotient` is an
isomorphism. The model family is exactly `unramifiedIntegerFacetModels` built
from the supplied apartment and `UnramifiedZeroDatum.ofConnectedReductive`.

This result does not construct a regular stable chamber, an integral split
source, or a pair model. It does not assert that units of a maximal split
torus fix an arbitrary prescribed point. Those remain separate parts of the
host fixed-point split-torus theorem.

## Implemented proof and provenance

This is derived internal content with no independent literature claim. The
actual published inputs are:

- `GaloisFacetCentroids`: an invariant original full facet meets the actual
  coefficient-fixed locus, by its canonical fixed centroid;
- `IntegerValuationAffineWeylProof`: the actual ordinary affine roots satisfy
  the affine-root-system axioms, including the rank-zero case, given an
  order-one unit;
- `IntegerBuildingMaximalFacets` and `AffineFacetRootCount`: strict upward
  full-facet incidence strictly decreases the finite vanishing-root count;
- `ConstructedMaximalGaloisFacetResidue`: an original maximal Galois facet has
  an actual recovered downstairs reductive quotient with no proper rational
  parabolics;
- `MaximalUnramifiedUniformizer`: the required order-one unit exists in the
  actual maximal unramified field.

First form the original full facet as the image of the supplied ordinary
apartment facet. Canonical coefficient equivariance of `D.apartmentMap`
turns its whole-facet stability into invariance of this same building
subset. The published fixed-centroid criterion then makes it a Galois
facet. The order-one unit is used only to obtain the actual affine-root-system
premise for that criterion.

The helper `isMaximalGaloisFacet_of_regular_apartmentFacet` proves maximality
without any further Galois geometry. Regularity means that no affine root
vanishes at `x`, so the facet's vanishing-root count is zero. If a different
original facet were incident above it, the published strict-decrease theorem
would give a natural number strictly below zero. Thus the original full
facet, and consequently its Galois facet, is already maximal.

Finally, `unramifiedStableChamberResidue` applies this construction using
the actual maximal-unramified order-one unit and invokes
`constructedMaximalGaloisFacetResidue` for this very `E`. It retains the
actual returned model recovery, valid quotient and no-proper-parabolic
conclusion. Neither chamber existence nor a transfer of split maximality
between different residue quotients enters this proof.
