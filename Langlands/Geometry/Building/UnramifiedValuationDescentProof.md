# Descent of the valuation of the root datum from the maximal unramified extension

Author: Worker 5553.

Lean module: `Langlands.Geometry.Building.UnramifiedValuationDescentProof`.

The theorem `Langlands.Geometry.Building.unramifiedValuationDescent` proves the published
proposition `Langlands.Geometry.Building.UnramifiedValuationDescentStatement` (module of the
same name) at arbitrary universe `u`. Its type is exactly
`UnramifiedValuationDescentStatement.{u}`. It adds no hypothesis and does not change the
statement.

## What is proved

Let `F` be a nonarchimedean local field, in either characteristic, and let
`K = inertiaFixedField F` be its maximal unramified extension. Take the data of the statement:

- a connected reductive `G` over `Spec F` with a maximal split torus `iS : S → G`;
- an `F`-torus `T ⊇ S` (`f : S ⟶ T`, `groupHom f ≫ iT = iS`) whose scalar extension `iT_K`
  is a maximal split torus of `G_K`;
- opposite factor pairs for `iT_K`;
- a class `D : KPApartmentData iT_K (IntegerValuation.order (MaximalUnramified.valuation F))`
  that satisfies V 6 for a centralizer datum `C` over `K`.

Write `fixed x` when `x : D.Apartment` is invariant under `RootFunctionFamily.galoisAction`
for every `σ : K ≃ₐ[F] K`. Write `φ x` for the torus-then-field restriction
`torusFieldRestrictedRootFunctionFamily` of `x` along the scalar extension of `f`. The theorem
gives `DS : KPApartmentData iS (localFieldOrder F)` and `CS : CentralizerDatum iS` such that:

1. `DS.IsOmegaCompatible CS`;
2. `DS.carrier = {φ x | fixed x}`;
3. `φ` is injective on fixed points;
4. for every `n : normalizerPoints iS` and every fixed `x` there is a fixed `y` with
   `D.apartmentMap y = rationalExtend n • D.apartmentMap x` in `D.ReducedBuilding` and
   `φ y = n • φ x`.

This is Kaletha–Prasad, Construction 9.6.1, Lemma 9.6.3 and Theorem 9.6.5, with §9.6.6 for
clause 3.

## Implemented proof

The proof term only composes published theorems of the Library; there is no tactic proof.
The outer step is the published reduction `unramifiedValuationDescent_of_fixedLocus` (module
`UnramifiedValuationDescentReduction`). It has type

`UnramifiedGaloisFixedApartmentStatement.{u} → UnramifiedFixedLeviTransportStatement.{u} →
UnramifiedFixedCentralizerCompatibilityStatement.{u} → UnramifiedFixedOppositeStatement.{u} →
UnramifiedValuationDescentStatement.{u}`.

That module's Markdown describes how the reduction builds `DS` and `CS` from one fixed point
`x0`. `DS` is `KPApartmentData.ofNormalizerShifts` of `φ x0`, and `CS` is
`CentralizerDatum.ofValuationComparison`. The four inputs are supplied as follows.

1. **Galois-fixed points exist** (KP §9.2.1). The input is `unramifiedGaloisFixedApartment`,
   module `UnramifiedGaloisFixedApartmentProof`.
2. **Levi transport at fixed points.** The proof builds a local term
   `hLevi : UnramifiedFixedLeviTransportStatement.{u}` (a `have`). Its value is
   `unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp`, module
   `UnramifiedFixedLeviTransportReduction`. That theorem proves
   `UnramifiedTorusUnitFixedApartmentStatement.{u} →
   UnramifiedLeviSharpApartmentTransportStatement.{u} → UnramifiedFixedLeviTransportStatement.{u}`.
   It is applied to two inputs:
   - The torus-unit fixed-apartment input (KP Proposition 9.3.13 over `K`) is
     `unramifiedTorusUnitFixedApartmentReduction`, module
     `UnramifiedTorusUnitFixedApartmentReduction`. That theorem proves
     `UnramifiedFixedPointTransporterStatement.{u} → UnramifiedTwistedFixedTranslationStatement.{u} →
     UnramifiedSplitTranslationFixerStatement.{u} → UnramifiedTorusUnitFixedApartmentStatement.{u}`.
     It is applied to three terms:
     - `unramifiedFixedPointTransporter_of_fixedPairSpecialApartment unramifiedFixedPairSpecialApartment`.
       The first theorem is in module `UnramifiedFixedPointTransporterReduction`. The second is
       KP Proposition 9.3.11(1), in module `UnramifiedFixedPairSpecialApartmentProof`.
     - `unramifiedTwistedFixedTranslation`, module `UnramifiedTwistedFixedTranslationProof`.
     - `unramifiedSplitTranslationFixer`, module `UnramifiedSplitTranslationFixerProof`.
   - The Levi-sharp transport input is `unramifiedLeviSharpApartmentTransport`, module
     `UnramifiedLeviSharpApartmentTransportProof`.
3. **V 6 on `Z_G(S)(F)` at fixed points.** The input is
   `unramifiedFixedCentralizerCompatibility_of_leviTransport hLevi`, module
   `UnramifiedFixedCentralizerReduction`. That theorem has type
   `UnramifiedFixedLeviTransportStatement.{u} → UnramifiedFixedCentralizerCompatibilityStatement.{u}`.
4. **V 5 at fixed points** (KP Proposition 9.4.9, Corollary 9.4.10). The input is
   `unramifiedFixedOpposite`, module `UnramifiedFixedOppositeProof`. That proof builds the same
   Levi transport term internally, from the same published theorems as item 2.

The module imports eleven Library modules: the reduction, the proof modules and reductions
named above, and nothing else. `lean_check` reports no errors or warnings. The theorem
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023): §9.2.1; Proposition 9.3.11
(printed p. 337); Proposition 9.3.13 (printed p. 338); Proposition 9.4.9 and Corollary 9.4.10
(printed pp. 349–350); Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5 and §9.6.6 (printed
pp. 365–368). The Lean proof follows the published reductions listed above, not one section of
the book.
