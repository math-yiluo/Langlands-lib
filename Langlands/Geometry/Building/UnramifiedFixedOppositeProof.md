# V 5 at the Galois-fixed points of the unramified apartment

The theorem `Langlands.Geometry.Building.unramifiedFixedOpposite` proves the published
proposition `Langlands.Geometry.Building.UnramifiedFixedOppositeStatement` (module
`Langlands.Geometry.Building.UnramifiedFixedLocusStatement`) at arbitrary universe `u`.
Its type is exactly `UnramifiedFixedOppositeStatement.{u}`. No hypothesis is added and the
statement is not changed.

In words: let `K` be the maximal unramified extension of a nonarchimedean local field `F`,
and take the data of `UnramifiedFixedOppositeStatement`. Let `x` be a point of the apartment of
`T_K` that is fixed by every `σ ∈ Aut(K/F)`. Then the torus-then-field restriction `φ x` of
the root-function family at `x` satisfies axiom V 5 of Kaletha–Prasad, Definition 6.1.2. That
is, `φ x (-a) g' + φ x a g = 0` whenever `g ∈ U_a(F)`, `g ≠ 1`, `g', g'' ∈ U_{-a}(F)` and
`g' g g'' ∈ N_G(S)(F)`. Mathematically this is Kaletha–Prasad, Corollary 9.4.10, as used in
the proof of Theorem 9.6.5. It follows from the last assertion of Proposition 9.4.9.

## Implemented proof

The proof term composes published theorems of the Library. It contains no new tactic proof.
From the outside in:

1. `unramifiedFixedOpposite_of_wallInvariance` (module `UnramifiedFixedOppositeReduction`)
   has type `UnramifiedFixedWallInvarianceStatement.{u} → UnramifiedFixedOppositeStatement.{u}`.
   This is KP's derivation of Corollary 9.4.10 from the last assertion of Proposition 9.4.9.
   The element `m(u)` fixes both walls, `{φ_a(u) = 0}` and `{φ_{-a}(u') = 0}`, and it reverses
   `a`. So the two walls coincide.
2. `unramifiedFixedWallInvariance_of_depthZero_of_leviTransport` (module
   `UnramifiedFixedWallInvarianceReduction`) proves
   `UnramifiedFixedWallInvarianceReductionStatement.{u}`, that is
   `UnramifiedFixedDepthZeroOppositeStatement.{u} → UnramifiedFixedLeviTransportStatement.{u} →
   UnramifiedFixedWallInvarianceStatement.{u}`.
3. The depth-zero input is `unramifiedFixedDepthZeroOpposite` (module
   `UnramifiedFixedDepthZeroOppositeProof`).
4. The Levi transport input is
   `unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp` (module
   `UnramifiedFixedLeviTransportReduction`). It proves
   `UnramifiedTorusUnitFixedApartmentStatement.{u} →
   UnramifiedLeviSharpApartmentTransportStatement.{u} → UnramifiedFixedLeviTransportStatement.{u}`.
   Its second input is `unramifiedLeviSharpApartmentTransport` (module
   `UnramifiedLeviSharpApartmentTransportProof`).
5. The torus-unit fixed-apartment input is `unramifiedTorusUnitFixedApartmentReduction` (module
   `UnramifiedTorusUnitFixedApartmentReduction`). It proves
   `UnramifiedFixedPointTransporterStatement.{u} → UnramifiedTwistedFixedTranslationStatement.{u} →
   UnramifiedSplitTranslationFixerStatement.{u} → UnramifiedTorusUnitFixedApartmentStatement.{u}`.
   This is KP Proposition 9.3.13 over `K`. It is applied to three proofs:
   - `unramifiedFixedPointTransporter_of_fixedPairSpecialApartment unramifiedFixedPairSpecialApartment`.
     The first theorem (module `UnramifiedFixedPointTransporterReduction`) proves
     `UnramifiedFixedPairSpecialApartmentStatement.{u} → UnramifiedFixedPointTransporterStatement.{u}`.
     The second (module `UnramifiedFixedPairSpecialApartmentProof`) proves the fixed-pair
     special-apartment statement, KP Proposition 9.3.11(1).
   - `unramifiedTwistedFixedTranslation` (module `UnramifiedTwistedFixedTranslationProof`).
   - `unramifiedSplitTranslationFixer` (module `UnramifiedSplitTranslationFixerProof`).

The module imports these ten modules and nothing else. It compiles with no errors or
warnings. The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023): Definition 6.1.2, axiom V 5
(printed p. 199); Proposition 9.3.11 (printed p. 337); Proposition 9.3.13 (printed p. 338);
Proposition 9.4.9 and Corollary 9.4.10 (printed pp. 349–350); proof of Theorem 9.6.5
(printed pp. 366–367). The Lean proof follows the published reductions listed above, not a
single section of the book.
