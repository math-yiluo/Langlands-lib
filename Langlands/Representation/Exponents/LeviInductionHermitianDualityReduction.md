# Hermitian duality for represented parabolic induction

Lean module: `Langlands.Representation.Exponents.LeviInductionHermitianDualityReduction`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques* (2026 version, literature
ID `renard-2026-representations-groupes-reductifs-padiques`), (IV.2.1.2) and IV.2.1,
Remarque 1 (both PDF p.103), as used in the proof of VII.1.3 (PDF pp.231–232). The
statement proved here is `LeviInductionHermitianDualityStatement` from
`Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`. Its Markdown
gives the source of each conclusion.

## Declaration

Namespace `Langlands.Aubert.General.RepresentedParabolic`.

- `leviInductionHermitianDuality_of_presentation (hC) (hUnimod) (hStandard) (hPres) :
  LeviInductionHermitianDualityStatement.{u, v}`, with premises:
  - `hC : ArbitraryParabolicQuotientCompactStatement.{u}`: for a parabolic `p : P ⟶ G`
    of a connected reductive `G` over a nonarchimedean local field, the quotient
    `P(F) \ G(F)` of the point image is compact;
  - `hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u}` and
    `hStandard : StandardCocharacterStatement.{u}`: the rational points of every
    connected reductive group are unimodular. The first statement derives this from the
    second;
  - `hPres : ParabolicRootPresentationExistenceStatement.{u}`: every parabolic `p` with
    rational Levi `l` and split component `a` of the Levi has a compatible
    `ParabolicRootPresentation p l a`.

  These are published statements. The Library has no unconditional proof of any of them
  yet, so the theorem is a conditional reduction.

  Proof. Fix the data of `LeviInductionHermitianDualityStatement`: `σ`, `χ`, `χ'` on
  `M(F)` and `W` on `G(F)`.

  1. Install the instances used by the generic theorem on `G(F)`: Hausdorff
     (`rationalPoint_t2Space`), Borel measurable space, and local compactness of the
     closed point image `pointImage p` (`isClosed_pointImage`). Compactness of the
     quotient is `hC k G hG P p hp`.
  2. Obtain the modulus identity of V.5.4 for `P(F)`. Put on `M(F)` the topology
     `leviPointTopology l hl`, which is Hausdorff (`rationalPoint_t2Space`), locally
     compact (`leviPoints_locallyCompactSpace`) and nonarchimedean
     (`leviPoints_nonarchimedeanGroup`). The proved `splitComponentStatement` gives a
     split component `a : A ⟶ M`, and `hPres k G hG P M A p l a hp hl ha` gives a
     presentation `pres`. Then `modularCharacter_of_presentation hG p l r hp hl hr hmul
     pres` (module `Langlands.Representation.Exponents.ParabolicPresentationUnitarity`),
     applied to the unimodularity `hUnimod k M hl.isConnectedReductive hStandard` of
     `M(F)`, says that the modular character of `P(F)` equals the Haar modulus of the
     conjugation action of `P(F)` on `U(F)`.
  3. `leviInductionFunctor p l r hp hr hl hmul` is by definition the normalized induction
     `normalizedInductionFunctor` for the semidirect decomposition
     `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul`. It is
     applied to the pullback along `e⁻¹`, where `e = leviPointsEquiv p l hp hl` is the
     topological group isomorphism from `M(F)` to the Levi point image
     `pointImage (l ≫ p)`. So `e⁻¹` maps the point image to `M(F)`.
  4. Apply `normalizedInduction_hermitianDuality` (module
     `Langlands.Representation.Aubert.General.NormalizedInductionHermitianDuality`) to
     this decomposition and to:
     - `σ₀ = SmoothRep.pullback e⁻¹ σ`. It is admissible by
       `isAdmissible_comp_continuousMulEquiv` and unitarizable via the pulled-back form
       `b.comp e⁻¹`.
     - `χ₀ = χ ∘ e⁻¹` and `χ₀' = χ' ∘ e⁻¹`. Their kernels are preimages of open sets
       under the continuous `e⁻¹`. The hypothesis `χ₀'(m) · conj(χ₀(m)) = 1` is the
       original one at `e⁻¹(m)`.

     The remaining inputs are:
     - `U(F)` closed (`isClosed_pointImage_comp`), `P(F)` closed, and the Levi
       projection continuous (`continuous_projection_pointImage`);
     - unimodularity `hUnimod k G hG hStandard`;
     - the modulus identity of step 2.

     The twist of the pullback, `σ₀ ⊗ χ₀`, is definitionally the pullback of `σ ⊗ χ`. So
     the conclusions of the generic theorem are, by definition, the two conclusions of the
     statement.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Derived. This is the specialization of the generic module to the represented-parabolic
interface. The premises supply the inputs Renard uses implicitly: compactness of `P \ G`
(VI.1.1, Remarque), unimodularity of reductive groups, and, through root presentations, the
modulus formula of V.5.4.
