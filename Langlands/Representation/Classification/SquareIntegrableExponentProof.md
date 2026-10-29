# The strict square-integrability criterion for normalized GL Jacquet exponents

Authors: Worker 19 and Worker 728. Worker 19 wrote the assembly and analytic
transport reductions. The private fundamental-tuple argument adapts Worker 728's
published `ProductLeviSquareIntegrable.strictFundHypothesis_of_core`.

`Langlands.glSquareIntegrableExponentCriterion` proves exactly the published
`Langlands.GLSquareIntegrableExponentCriterionStatement.{uF,uV}`. For every
positive-rank GL over the supplied finite p-adic field, a nonzero admissible
representation with the specified scalar character is square integrable modulo
its centre if and only if that character is unitary and every actual normalized
standard-upper Jacquet exponent has norm below one on every nonconstant
monotone block-scalar tuple. The field and representation-carrier universes are
independent. There is no irreducibility or finite-dimensionality assumption.

The analytic predicate is unchanged: it quantifies every Borel Haar measure on
the actual quotient by the centre and every smooth-dual matrix coefficient.
The exponent predicate is the existing open-kernel, uniform common-power
generalized occurrence in the actual normalized Jacquet module. Both standard
and refined Jacquet actions retain their inverse-half-modulus normalization.

## Implemented analytic reductions

For an arbitrary one-block shape `C`, let `σ` be `ρ` pulled back through the
actual `C.leviEmbedding`. The proof first supplies four private reductions.

1. `squareIntegrable_singleBlock_pullback` transports the all-Haar GL predicate
   to any supplied Borel Haar measure on the one-block Levi's central quotient.
   It uses `C.singleBlockLeviEquivContinuous` and the proved generic theorem
   `isSquareIntegrableModCenter_comp_continuousMulEquiv`. Thus the groups, centre
   quotients and coefficient functions are the actual published constructions.
2. `singleBlock_core_of_squareIntegrable` chooses an existing Haar measure on
   the GL quotient, pushes it forward through the inverse quotient equivalence,
   and applies `glProductLeviSquareIntegrableExponentNecessity` to `σ`.
   The result retains every refinement, the open kernel and uniform generalized
   occurrence. It bounds exponents on the whole blockwise monotone chamber,
   with strictness whenever one original block has unequal absolute values.
3. `strictFundHypothesis_of_strict` derives `StrictFundHypothesis` using only
   the strict bound on such nonconstant tuples. Smoothness gives an open kernel
   for every generalized character of the refined scalar action. A fundamental
   tuple is blockwise monotone and has entries of absolute values `q⁻¹` and `1`
   in the selected block. These differ since `q > 1`, so the strict premise
   applies. This specializes Worker 728's argument by omitting its unused
   weak conjunct.
4. `squareIntegrable_of_singleBlock_strictFundHypothesis` pulls admissibility
   and a genuine unitary central character back to `σ`. For each GL quotient
   Haar measure, the published
   `ProductLeviSquareIntegrable.memLp_two_of_strictFundHypothesis`, supplied
   with the proved `CartanQuotient.cartanCellCount`, gives every coefficient in
   L2 for its pushforward measure on the Levi quotient. Pullback through the
   inverse continuous group equivalence recovers `ρ` and the original measure.

The fourth step uses the arbitrary admissible representation helper, rather
than the separate closed product-Levi sufficiency statement with its
irreducibility hypothesis. The helper obtains a strict exponential margin
beyond the half-modulus separately for each coefficient. Squaring and
multiplying by the inverse-modulus Cartan volume bound leaves a summable
geometric lattice series. No global finite Jacquet spectrum or substitution
of an integrability exponent below two is assumed.

## Ordinary and refined exponent assembly

Choose the published shape
`C := CuspidalSupport.LeviAdmissibility.oneBlock n hn`.
Its Levi is the actual GL group through the continuous equivalence above.
Every standard block shape is `B := C.singleBlockRefinementEquiv hC D` for
some refinement `D`. Write `e` for `C.singleBlockScalarMulEquiv hC D F.Carrierˣ`;
its ordinary coordinate `j` is the flattened coordinate at
`C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩`.

The published `SingleBlockJacquetTransport` constructs the comparison on the
actual quotients, sending the class of each vector to the class of the same
vector. Its scalar equivalence preserves the common natural power and open
kernel. Its ordered scalar coordinates identify blockwise monotonicity with
ordinary monotonicity. Nonconstancy is transported at the unique outer block.

For necessity, `glSquareIntegrableCentralCharacter` first forces the supplied
scalar character to have norm one; nontriviality of the carrier identifies it
with the analytic central character. Given any standard exponent `χ` and
ordinary tuple `a`, the proof uses
`singleBlock_isJacquetExponent_iff` to obtain the refined exponent `χ ∘ e`
and evaluates it at `e.symm a`. The monotonicity correspondence and a witness
of unequal absolute values supply the hypotheses of the second reduction.
Its strict conclusion is exactly `‖χ a‖ < 1`.

For sufficiency, the same central-character theorem constructs a
`UnitaryCentralCharacter ρ` from scalar unitarity and smoothness. For any
refinement and flattened character `ψ` with open kernel and generalized
occurrence, `singleBlock_isJacquetExponent_iff_flattened` makes
`ψ ∘ e.symm` an actual standard Jacquet exponent. The assumed strict standard
bound at `e a` is precisely the required refined bound at `a`. The third and
fourth reductions give square integrability for every Haar measure.

All block shapes remain quantified. When the relevant shape has one block,
the nonconstant chamber is empty. The proof obtains and uses scalar unitarity
separately, so that empty chamber does not remove the central-character
condition.

## Provenance

The target's original source is Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups*, 1 May 1995,
Theorem 4.4.6, printed/PDF p.45, with its discussion on pp.44–45.
The registered source is `casselman-1995-admissible-representations`,
SHA256 `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
Waldspurger's *La formule de Plancherel pour les groupes p-adiques*, 2003,
Proposition III.1.1, printed p.263, gives the corresponding normalized
formulation; §I.3, printed p.243, fixes the normalization. Its registered
source is `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The source conventions and their GL specialization are documented in the
unchanged target Markdown. This proof assembles proved Library analytic and
geometric results; its transport reductions are internal deductions from the
actual definitions. A source citation is not used as a Lean premise.

## Dependency and independence audit

At Library base `9076dbdeff7e1d9a1bddd23c2f62e11d180814a1`, native import
traversal gives 398 project modules including this new entry. Every module has
nonempty paired Markdown. Every imported Lean/Markdown pair is byte-identical
to that Library, including the target and everything it imports.

The eight direct imports are the target statement,
`SquareIntegrableCentralCharacterProof`,
`ProductLeviSquareIntegrableExponentNecessityProof`,
`ProductLeviStrictCoefficientL2Proof`, `InverseTransposeAnalyticProof`,
`Geometric.SingleBlockJacquetTransport`, `Group.GL.SingleBlock` and
`Group.GL.OneBlockShape`, under their respective `Langlands.Representation`
or `Langlands` prefixes.

The previously audited analytic closure is unchanged. Adding the published
comparison adds only `SingleBlockJacquetTransport` and the generic
`Filtration.GeneralizedEigencharacterStatement` and
`Filtration.GeneralizedEigencharacterProof`. The comparison uses actual
quotient lifts, group embeddings, the explicit modulus and scalar coordinate
equivalences. The filtration helpers preserve uniform character spaces under
intertwiners and equivalences; they introduce no classification premise.

The closure contains no proof or mathematical conclusion of the excluded
segment analytic classification, multisegment special-head exhaustion,
ordered special-head existence or quotient coverage, tempered block uniqueness,
square-integrable Langlands classification or exhaustion, or regular
exhaustion. It also contains no proof of weakly-critical support, refinement or
minimality, tempered discrete-series support, exhaustion, unitarity or
genericity, or equal-exponent grouping.

Some imported modules define segments, supercuspidal support and neighboring
tempered statements. The only text hits for the excluded tempered support and
unitarity names are unproved `Prop` definitions and their aggregate
definitions in `TemperedSupportStatement` and `TemperedInductionStatement`.
They supply no theorem-valued assumption. The proof imports neither
`SegmentQuotientJacquetSingleBlock` nor its segment classification dependencies.
The generic analytic transport module contributes centre, dual, coefficient
and group-equivalence laws, without an excluded classification conclusion.

Development compilation and declaration inspection succeeded in the approved
environment. Inspection reports the independent level parameters `uF`, `uV`
and only `propext`, `Classical.choice`, and `Quot.sound`. The theorem has the
named proposition as its complete type, without extra theorem-valued premises.
