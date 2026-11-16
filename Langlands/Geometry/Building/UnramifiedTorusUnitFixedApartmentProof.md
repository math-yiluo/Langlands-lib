# Torus-unit-fixed coefficient-fixed points lie in the fixed special apartment

The theorem
`Langlands.Geometry.Building.unramifiedTorusUnitFixedApartment.{u}` proves
exactly the published proposition
`Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement.{u}`.
It has no additional hypotheses, holds at every universe `u`, and applies in
both characteristics.

For the published data over a nonarchimedean local field \(F\), put
\(K=\operatorname{inertiaFixedField}(F)\). A point of the reduced
root-valuation quotient building that is fixed by every coefficient
automorphism of \(K/F\) and by the entire character-valuation kernel in
\(S_K(K)\) is the apartment image of a coefficient-fixed point of the
special \(T_K\)-apartment. The original full V6 compatibility hypothesis
and Galois-stability hypothesis are retained. The apartment preimage is
fixed as an underlying root-function family, as the statement requires.

## Implemented proof and published inputs

The Lean proof applies
`Langlands.Geometry.Building.unramifiedTorusUnitFixedApartmentReduction`
from `Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentReduction`
to these three unconditional published theorems, all at the same universe `u`:

1. `Langlands.Geometry.Building.unramifiedFixedPointTransporter`, from
   `Langlands.Geometry.Building.UnramifiedFixedPointTransporterProof`.
   It supplies a transporter \(h\) centralizing \(S_K(K)\), fixing a
   coefficient-fixed apartment base point, with
   \(h^{-1}\sigma(h)\in N(T_K)(K)\), and expressing the given point as
   \(h\cdot[x_1]\).
2. `Langlands.Geometry.Building.unramifiedTwistedFixedTranslation`, from
   `Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof`.
   It puts the resulting twisted-fixed difference \(x_1-x_0\) in
   `splitTranslationDirections`, the image of \(V(S_K)\) in the reduced
   translation space.
3. `Langlands.Geometry.Building.unramifiedSplitTranslationFixer`, from
   `Langlands.Geometry.Building.UnramifiedSplitTranslationFixerProof`.
   It proves that a centralizing element fixing \([x_0]\) fixes every
   split translation of \([x_0]\), hence fixes \([x_1]\).

The reduction obtains \(x_0\) from the published
`Langlands.Geometry.Building.unramifiedGaloisFixedApartment` and apartment
injectivity from `KPApartmentData.apartmentMap_injective`, after applying
`Langlands.GroupScheme.connectedReductiveFieldExtensionStatement` to
\(G_K\). Semilinearity and injectivity turn coefficient fixation of
\(h\cdot[x_1]\) into twisted fixation of \(x_1-x_0\). The three inputs then
give \(y=[x_1]\). Finally, coefficient fixation of \(y\) and apartment
injectivity give coefficient fixation of \(x_1\) itself.

This module is a derived composition of those published results. It uses
none of `UnramifiedGaloisFixedBuildingPointStatement`,
`UnramifiedBuildingDescentStatement`,
`UnramifiedBuildingDescentReductionStatement`,
`UnramifiedBuildingDescentRemainingReductionStatement`, or theorems
consuming them as proof inputs.

## Source provenance

The target and the reduction formulate Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Proposition 9.3.13, printed p.338 (PDF p.369),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The transporter input corresponds to Propositions 9.3.11(1) and 9.3.12.

The proof incorporates the independence of split translations supplied
before Proposition 9.3.13 in the authors' *Corrections and additions*,
version of 1 November 2024, PDF pp.39–41, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
That argument is implemented in the third input through valuation
translations, commuting orbits, and finite convex combinations. The
present proof uses this corrected input through the published reduction.
