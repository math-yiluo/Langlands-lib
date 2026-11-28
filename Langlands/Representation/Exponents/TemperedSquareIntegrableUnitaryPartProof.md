# Square-integrability of tempered representations through unitary Jacquet parts: proof

Module `Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

`temperedSquareIntegrableUnitaryPart` proves exactly the published proposition
`TemperedSquareIntegrableUnitaryPartStatement.{u, v}` (module
`Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement`)
at arbitrary field universe `u` and representation-carrier universe `v`.
[Statement](TemperedSquareIntegrableUnitaryPartStatement.md)

The proposition is the Lemma of VII.2.4 of David Renard, *Représentations des
groupes réductifs p-adiques*, French edition dated 9 July 2026, printed p.230 /
PDF p.236 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`): a tempered
representation `π` of `G(F)` with a central character `ω` is square integrable
modulo the center, for a given Haar measure on `G(F) ⧸ Z(G(F))`, if and only if
the unitary Jacquet part `(r_P^G π)_0` vanishes at every proper parabolic `P`. In
the Lean proposition, `P` ranges over every actual rational parabolic `p` with
`¬ IsIso p`, with every rational Levi, matching geometric unipotent radical and
split component.

The theorem has no hypotheses. It keeps every quantifier of the proposition:
every nonarchimedean local field `k : Type u` with its valuation, topology and
Hausdorff instances, every connected reductive `G`, the canonical point topology
on `G(k)` with the local-compactness and nonarchimedean-group instances, every
Borel measurable structure and Haar measure on `G(k) ⧸ Z(G(k))`, every smooth
complex representation `π` with carrier in universe `v`, and every central
character `ω`, which is not assumed unitary. It adds no standardness of the
parabolics, no admissibility beyond the admissibility contained in
`IsNormalizedExponentTempered`, and no finite-length, irreducibility,
presentation-existence, Jacquet-admissibility, quotient-compactness or
Iwahori-contraction premise. The Lean check reports the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Results

- `unitaryJacquetPart_eq_bot_of_tempered_squareIntegrable`: the forward
  direction, stated for one field and one group. If `π` is tempered
  (`IsNormalizedExponentTempered hG π`) and
  `IsSquareIntegrableModCenter π.representation haar`, then
  `unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥` for every actual rational
  parabolic `p` with `¬ IsIso p`, every rational Levi, matching radical and
  split component. No central-character hypothesis is needed, because the
  published predicate `IsSquareIntegrableModCenter` already contains a unitary
  central character.
- `temperedSquareIntegrableUnitaryPart_of_casselmanSufficiency`: the
  implication `ArbitraryParabolicCasselmanSufficiencyStatement.{u, v} →
  TemperedSquareIntegrableUnitaryPartStatement.{u, v}`.
- `temperedSquareIntegrableUnitaryPart`: the proposition itself.

## The implemented proof

1. **Forward direction.** The published theorem
   `arbitraryParabolicCasselmanNecessity` (module `CasselmanNecessity`) is the
   necessity half of Casselman's criterion (Renard VII.1.2) for actual
   parabolics. Applied to `G`, the Haar measure and `π`, it turns square
   integrability into the cone condition `HasPositiveRepresentedJacquetExponents
   π` (module `CasselmanSufficiencyAssembly`): at every actual parabolic, Levi,
   matching radical, split component and compatible `ParabolicRootPresentation`,
   every normalized Jacquet exponent has normalized real part in the strictly
   positive root cone. For tempered `π`, the forward implication of the published
   `hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish`
   (module `TemperedPositiveJacquetExponents`) turns this condition into the
   vanishing of every proper unitary Jacquet part. That implication takes the
   compatible presentation contained in temperedness and uses that the zero
   real part does not lie in the strictly positive cone of a proper parabolic.
2. **Reverse direction from sufficiency.** Let all proper unitary Jacquet parts
   vanish. Admissibility of `π` is a component of temperedness
   (`IsNormalizedExponentTempered.isAdmissible`). A unitary central character is
   the published construction `IsNormalizedExponentTempered.unitaryCentralCharacter`
   (module `TemperedCentralCharacterData`): for nonzero `π` it keeps `ω`, which
   is unitary by the published `normalizedTemperedCentralCharacter` (Renard
   VII.2.1, Remark 1) and has an open kernel by smoothness; for zero `π` it is
   the trivial character. The reverse implication of
   `hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish`
   turns the vanishing into the cone condition. Its proof is the argument of the
   source: an exponent whose real part lies in the closed cone but not in the
   open one gives an actual proper parabolic containing `P` with a nonzero
   unitary Jacquet part. The sufficiency half of Casselman's criterion,
   `ArbitraryParabolicCasselmanSufficiencyStatement` (module
   `CasselmanSufficiencyReduction`), then gives square integrability modulo the
   center for the given Haar measure.
3. **Sufficiency.** The published
   `arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis` (module
   `CasselmanSufficiencyReduction`) derives
   `ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}` from
   `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`,
   through the strict Jacquet square-integrability theorem
   `RationalPointFamily.rationalStrictJacquetSquareIntegrabilityReduction`.
   The Bruhat–Tits statement is proved in the Library by
   `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
   (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`): one special
   vertex of the building gives the special compact subgroup, the Iwasawa and
   Cartan decompositions and the simultaneous standard basis of Renard
   V.5.1–V.5.2, the inputs of the source proof of sufficiency in VII.1.2. The
   Lean term of the main theorem is

   ```
   temperedSquareIntegrableUnitaryPart_of_casselmanSufficiency
     (arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis
       BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence)
   ```

## Relation to the source proof

Renard's proof cites the definitions, Remark 1 of VII.2.1 and Casselman's
criterion. The Lean proof uses the two halves of the criterion separately: the
proved necessity half for the forward direction and the sufficiency half for the
reverse direction. The passage between the cone condition and the vanishing of
the unitary parts, which the source leaves to the definitions, is the published
comparison `hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish`.
It works directly with all actual parabolics, so no reduction to standard
parabolics is needed for the quantifier over `P`.

The full Casselman criterion `ArbitraryParabolicCasselmanCriterionStatement` is
not used, and this file does not prove it.
