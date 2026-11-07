# Supercuspidal partners of selected tempered blocks

Worker 1779 authored the bridge; Worker 1743 specified the retained selected
block and centered-segment interface for the separate rank argument and the
direct genericity argument used below.

This internal contribution supports `TemperedTwistSupercuspidalPoleStatement`.
It derives a full untwisted pair-polynomial pole certificate under the three
explicit JPSS formulas and tempered block exhaustion. It retains the
classification witnesses needed for a separate rank argument. It does not
prove the unconditional target, a rank bound, or a change of partner universe.

The module uses `F : PadicField.{uF} p`, its canonical topological data
`T`, a unitary additive character `ψ`, and a self-dual Haar measure `ν` for
that character. Write `α = |det|`. All blocks, centered seeds and constructed
partners have carriers in `Type (max uF uV)`. The original representation
has its carrier in `Type uV`.

`HasSelectedBlockPole F ψ ν k τ` is a proposition with these witnesses:

- `l`, `m : Fin l → ℕ` and the exact identity
  `∑ j, (m j + 1) = k + 1`;
- irreducible, square-integrable, unitarizable smooth blocks `σ j` of rank
  `m j + 1` and an actual representation equivalence
  `τ ≃ i(σ j)` for the canonical normalized product induction;
- a selected index `i : Fin l`, natural numbers `a,d`, the exact identity
  `∑ _ : Fin (d + 1), (a + 1) = m i + 1`, and an irreducible supercuspidal
  smooth seed `π₀` of rank `a + 1` whose centered normalized induction
  contains `σ i` as an irreducible component;
- an irreducible supercuspidal smooth partner `ρ` of rank `a + 1` and
  `HasPadicRankPoleAtZero F ψ ν τ.representation ρ.representation`.

The last proposition, imported from `TemperedSupercuspidalPoleAssembly`,
means that there is `P : ℂ[X]` with the complete
`IsPadicRankLPolynomial F ψ ν.val τ.representation ρ.representation P`
certificate and `P.IsRoot 1`. The selected index, exact rank equalities and
component certificate remain available in this existential conclusion.
The proposition itself has no formula or exhaustion premise;
`hasSelectedBlockPole_of` proves it with those premises.

`exists_partner_of_centered_component` supplies the partner for a given
essentially square-integrable block with the supplied centered-component
certificate. Its hypotheses retain (8.1)(ii) as
`SupercuspidalEqualRankLFactorStatement` and (8.2) as
`SquareIntegrableLFactorStatement`, at the displayed maximum carrier
universe. Its conclusion also retains essential square-integrability of `ρ`
and the complete pair-polynomial certificate and root for `σ × ρ`.

The implemented proof bundles the top centered factor `α^(d/2) π₀`
as `top` and sets `ρ = top.contragredient`.
`isIrreducible_centeredSegmentBlocks` and
`isSupercuspidal_centeredSegmentBlocks` give the properties of `top`.
`SmoothRep.isIrreducible_contragredient_iff`, using the proved
`compactOpen_cofinal` for GL, and
`GeneralLinear.isSupercuspidal_smoothContragredient` give irreducibility and
supercuspidality of `ρ`. `SmoothRep.bidualIso` gives the equivalence of
`top` with the smooth contragredient of `ρ`. The proved
`Whittaker.SupercuspidalKirillovProof.exists_functional` gives a nonzero
Whittaker functional on `ρ`. Its irreducibility and admissibility, the latter
included in supercuspidality, then give genericity.
`isOfWhittakerType_of_isGeneric` from `GenericModel` gives Whittaker type of `ρ`.
The classification helper
`supercuspidal_isEssentiallySquareIntegrable` gives its essential
square-integrability. The imported conditional assembly
`exists_squareIntegrable_isRoot_one` then applies (8.1)(ii) and (8.2).

`hasSelectedBlockPole_of` first applies
`temperedSquareIntegrableBlockDecomposition` to the supplied irreducible
tempered `τ`, with `TemperedBlockExhaustion.{uF,uV} F T` kept explicit.
The positive total rank makes `l` positive, so the proof selects index zero.
The selected block is essentially square-integrable by exponent zero;
`essentiallySquareIntegrableCenteredSegmentComponent` supplies its seed
and component data. The preceding partner lemma supplies `ρ` and a block
polynomial `R` with `R.IsRoot 1`.

To apply the product formula, unpack essential square-integrability of `ρ`
as `∃ z, T.IsSquareIntegrable (α^(-z) ρ)`. Bundle the latter representation
as `γ = T.segmentFactor ρ (-z)`. Character twisting preserves
irreducibility, smoothness is carried by this bundled twist, and
`realPowerTwist_cancel_neg` reconstructs `α^z γ = ρ`.
The centered rank identity gives `a ≤ m i` by
`le_iff_of_centeredSegment_rank`, allowing the block certificate to be read
through the symmetric arbitrary-rank interface. Finally,
`exists_induced_isRoot_one` applies the explicit
`TemperedLFactorStatement` (8.4), with common twists `0` and `z`, and the
actual induction equivalence. The reconstruction equality and zero twist
identify the resulting pole with the pair `τ × ρ`.

The provenance is internal composition of the imported classification
bridges, smooth-duality and Kirillov proofs, and conditional polynomial
assembly. The classification bridge is the contribution of Workers 1722
and 1779 in `TemperedTwistSupercuspidalPoleClassification`; it is imported
without copying or modifying its proofs. No additional external
mathematical input is introduced. In particular, the proof does not assume
that the dual of a square-integrable representation is square-integrable:
normalization uses the already proved essential square-integrability of
the supercuspidal partner.

The retained obligations are the actual tempered block exhaustion and
the JPSS (8.1)(ii), (8.2) and (8.4) formula proofs. Rank bounds,
transport to an independent partner universe, and removal of an arbitrary
real twist from `τ` belong to the separate final adapter.
