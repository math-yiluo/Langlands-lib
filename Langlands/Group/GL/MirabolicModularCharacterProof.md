# The modular character of the actual mirabolic group

The Haar-uniqueness, central-Levi comparison and scalar-character extension
adapt the published block-parabolic argument in `Group/GL/ParabolicModularCharacter`.
The compact slices and the algebraic proof on the radical are implemented here
for the actual mirabolic subgroup. The import closure of the radical
Haar-scaling dependencies was audited as well.

## Exact result

The theorem `Langlands.mirabolicModularCharacter` in
`Langlands.Group.GL.MirabolicModularCharacterProof` has the unapplied type

```lean
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  Langlands.MirabolicModularCharacterStatement.{uF} F T
```

Its only universe parameter is `uF`. Its axioms are exactly `propext`,
`Classical.choice` and `Quot.sound`. The theorem proves the unchanged published
proposition in [MirabolicModularCharacterStatement](MirabolicModularCharacterStatement.md).
There are no extra parameters, instances, hypotheses, universe constraints,
chosen Haar normalizations or theorem-valued arguments. Compilation
and declaration inspection succeed without errors or warnings.

For every `n : ℕ` and `g : GeneralLinear.mirabolic n F.Carrier`, it gives

```lean
MeasureTheory.Measure.modularCharacter g =
  ((T.determinantNorm (n + 1) g.val : ℝ≥0ˣ) : ℝ≥0)
```

The group is the actual subgroup of `GL_(n+1)(F)` with last row
`(0, …, 0, 1)`. Thus Lean rank `n` corresponds to BZ77's `P_(n+1)`.
All ranks are covered, including `n = 0`: both the radical and `GL_0` are
trivial, and the determinant and both character values are one. No positive-rank
hypothesis is hidden in a helper. In particular, the determinant expansion and
the published general-linear character theorem both allow an empty index type.

## Source and orientation

Registered source: `bernstein-zelevinsky-1977-induced-i`, I. N. Bernstein and
A. V. Zelevinsky, *Induced representations of reductive p-adic groups. I*,
Ann. Sci. ÉNS (4) 10 (1977), 441–472. The source file is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The passages used are §1.7, printed p.444 (one-based PDF p.5); §3.1, printed
p.450 (PDF p.11); and the opening sentence of §4.2, printed p.454 (PDF p.15).
These passages were read, with the formulas on PDF pp.5 and 15 also checked in
the rendered originals. No corresponding errata entry was found in the project
or published notes.

Section 1.7 defines the module of an automorphism using its inverse in the
integrand, and sets `Δ_G = mod_G⁻¹`. Section 3.1 defines the last-row mirabolic
subgroup and its standard general-linear Levi and last-column radical.
Section 4.2 defines `ν(g) = |det g|` using the standard field norm and records
`Δ_P = ν⁻¹|_P`, without supplying a proof. Only this preliminary modular
identity is relevant here; the representation-theoretic results on the same
pages supply no proof input.

Mathlib's `modularCharacter g` is the scalar in
`map (· * g) μ = modularCharacter g • μ` for a left Haar measure. Left
invariance identifies this with the scalar for the integral
`∫ f(g⁻¹ x g) dμ(x)`, namely BZ77's `mod_G(g)`. Therefore the target is
**positive** `|det g|`, the inverse of BZ77's `Δ_P`. The radical input has
`μ.map Ad(m) = |det m|⁻¹ • μ`; taking `m⁻¹` in the compact-slice comparison
produces the positive `|det m|` on the full group.

The formal proof is an internal derivation of the published statement, rather
than a transcription of a proof in BZ77. The determinant comparison is proved
by matrix algebra here; the source is not used as an assumption for it.

## Supplied topology and side hypotheses

The closing theorem installs exactly `T.topology`. It also installs
`T.valuativeRel`, `T.localField`, `T.fieldT2` and
`T.secondCountableTopology`. These certificates concern that same supplied
topology. In particular, they provide the topological ring structure used by
the coordinate maps. The theorem never substitutes a different field topology.

For each rank, `T.generalLinearTopologicalGroup (n + 1)` and
`T.generalLinearLocallyCompactSpace (n + 1)` are the instances in the published
statement. The Levi's local compactness is
`T.generalLinearLocallyCompactSpace n`. The mirabolic's local compactness is
the published `GeneralLinear.Mirabolic.locallyCompactSpace`, obtained from
closedness in `GL_(n+1)`. The radical is closed in the mirabolic, so it too is
locally compact. These proof-valued certificates may be reconciled by proof
irrelevance; the topologies themselves remain fixed.

Second countability of `GL_(n+1)` is derived, not assumed: finite products of
the second countable field give the matrix space, the opposite matrix space
inherits second countability through `MulOpposite.opHomeomorph`, and
`Units.isInducing_embedProduct` transfers it to matrix units. Subspaces then
give second countability of the mirabolic and its radical. The proof does not
import the larger project countability development.

The comparison helpers install the Borel structures of these topologies and
choose their Haar measures internally. The supplied radical scaling theorem
uses the same Borel radical and `T` and holds for every radical Haar measure.
The arbitrary compact slices are chosen using local compactness. No compact
integral subgroup, contraction, chosen normalization or measure-existence
premise is added to the final theorem.

## Implemented proof

Write `P = GeneralLinear.mirabolic n K`, `V = radical n K`,
`L = GeneralLinear n K`, `ι = levi` and `π = projection`.

1. **Coordinates and determinant.** The private `radicalPart` sends `g` to
   `radicalElement (lastColumn g)`. Published mirabolic decomposition gives
   `radicalPart(g) = g ι(π(g))⁻¹`. Its projection is trivial on `V`, and
   `radicalPart(u g) = u radicalPart(g)` for `u ∈ V`. The private
   `partsHomeomorph` identifies `P` with `V × L` by these two parts, with inverse
   `(u,m) ↦ u ι(m)`. Both directions are continuous for the actual subspace
   topologies. Consequently each slice `π⁻¹(C) ∩ radicalPart⁻¹(E)` is exactly
   the image of `E × C`. Separately, `det_lastRow` applies
   `Matrix.det_succ_row` to the last row. Only the last cofactor survives;
   its sign is `(-1)^(2n) = 1`, and its minor is the upper-left block.
   The public `determinant_projection` lifts this equality to determinant units
    and is reused by the mirabolic restriction factors.

2. **Triviality on the radical.** `character_radical` proves this for every
   homomorphism `χ : P →* ℝ≥0`, without topology. Conjugation by the Levi scalar
   `-1` sends a radical element with coordinate `v` to the one with coordinate
   `-v`, its inverse. Character values are invariant under conjugation, so
   `χ(u) = χ(u⁻¹)` and `χ(u)^2 = 1`. Nonnegativity implies `χ(u) = 1`.
   This applies to Mathlib's actual modular character. The proof also works in
   characteristic two and in rank zero.

3. **Haar measure on a compact Levi slice.** For Haar measures `ν` on `P`
   and `μ` on `V` and compact `C ⊂ L`, put
   `ρ = (ν.restrict (π⁻¹(C))).map radicalPart`.
   Left multiplication by a radical element preserves `π⁻¹(C)` and transports
   `radicalPart` by left multiplication. Thus `ρ` is left invariant.
   For compact `E ⊂ V`, the slice formula identifies its preimage with the
   continuous image of the compact product `E × C`; hence `ρ(E)` is finite.
   Mathlib's `isMulLeftInvariant_eq_smul` gives `ρ = c • μ` for a finite
   nonnegative real `c`. This is the private
   `map_radicalPart_restrict_eq_smul`; it imposes no positivity on `c` in advance.

4. **Central Levi comparison.** Suppose `m ∈ L` commutes with all of `L`.
   Then `π(ι(m)⁻¹ g ι(m)) = π(g)` and the radical coordinate is transformed by
   `Ad(ι(m⁻¹))`. Choose compact sets `U ⊂ V` and `C ⊂ L` with nonempty
   interiors. The homeomorphism makes their image `S ⊂ P` compact with nonempty
   interior. The preceding Haar comparison yields `ν(S) = c μ(U)`.
   `ModularCompactAverage.measure_preimage_conj` computes the conjugation
   preimage of `S` as `modularCharacter(ι(m)) ν(S)`. The coordinate formula
   and radical scaling law compute the same quantity as `δ(m) c μ(U)`.
   The common factor is `ν(S)`, which is strictly positive by nonempty
   interior and finite by compactness. `ENNReal.mul_left_inj` cancels it.
   This proves the private `modularCharacter_levi_of_commute` with the positive
   factor `δ(m)`. It uses no quotient integration or product-Haar formula.

5. **Every Levi element.** The character
   `χ(m) = modularCharacter(ι(m)) · δ(m)⁻¹` is one on scalar matrices by the
   central case. The published purely algebraic
   `RankinSelberg.GeneralLinearUnimodularity.character_eq_one` makes it one
   everywhere. That theorem uses permutation conjugacy of one-coordinate
   diagonals, positive powers, conjugacy of transvections to their inverses,
   and Mathlib's diagonal/transvection matrix induction. It needs neither
   topology nor a nonempty index type. This proves `modularCharacter_levi`.

6. **Closing the exact target.** Take `δ = T.determinantNorm n` and discharge
   its entire Haar-scaling premise with the published
   `GeneralLinear.Mirabolic.radicalHaar_map_leviConj F T n`. Decompose
   `g = radicalPart(g) ι(π(g))`; multiplicativity, step 2 and step 5 give
   `modularCharacter(g) = T.determinantNorm n (π(g))` in `ℝ≥0`.
   Apply `T.normalizedAbsUnits` to `determinant_projection` to identify this
   with `T.determinantNorm (n+1) g.val`, exactly the published conclusion.

All auxiliary declarations in this module are private. Their provenance is
internal matrix/group algebra, the compact-slice adaptation just described,
and the cited published Library and pinned Mathlib results. The generic
helpers' local Haar-scaling premise is fully discharged in the closing theorem.
No unpublished result is used as a mathematical premise.

## Complete import and mathematical dependency audit

The five direct imports are
`Group.GL.MirabolicModularCharacterStatement`, `Group.GL.MirabolicModulusProof`,
`Group.GL.MirabolicProjection`,
`Representation.RankinSelberg.GeneralLinearUnimodularity` and
`Analysis.Local.ModularCompactAverage`, all under `Langlands`.
Their complete transitive project closure contains the following **36** modules
(excluding the present proof). All corresponding Lean/Markdown pairs were checked
byte for byte against the published Library base
`81727e81ea12b8e578930ab79e9857e01bf72975`; none is edited by this module.
The original target pair also retains its pinned hashes.

| Family under `Langlands` | Complete modules in that family | Mathematical role and independence check |
| --- | --- | --- |
| `Group.GL` | `Basic`, `UpperUnipotent`, `Mirabolic`, `RankMaps`, `MirabolicRadical`, `MirabolicProjection`, `Padic`, `NormalizedCharacter`, `MirabolicModularCharacterStatement`, `MirabolicModulusStatement`, `MirabolicModulusProof` | Actual matrix groups, block/rank coordinates, closedness, topology and determinant norm; radical conjugation is transported to ordinary matrix multiplication. No representation-theoretic conclusion occurs. |
| `LocalField` | `Definitions`, `Canonical`, `Topology`, `Normalization.Definitions`, `Normalization.Statement`, `Normalization.Proof` | Finite extensions of `ℚ_p`, the supplied valuative topology, residue cardinality, discrete order and normalized absolute value. The normalization proof uses valuation, residue-field, finite-dimensional and ramification algebra from Mathlib. Its spectral-norm/topology comparisons are proved from `T`, rather than assumed here. |
| `HarmonicAnalysis` | `Basic`, `PadicHaarScalingStatement`, `PadicScalarHaarScalingProof`, `PadicRectangularHaarScalingProof` | Elementary character/Haar definitions and actual additive Haar scaling. Scalar scaling computes the residue-normalized factor on the integer ring and its maximal ideal, then handles units and uniformizer powers. Matrix scaling uses finite product Haar measures and diagonal/transvection induction. No derivative or classification result is involved. |
| `Group` | `HaarModulus` | Conjugation on the actual normalizer and Mathlib's `mulEquivHaarChar`, with closed-subgroup wrappers. Its open-kernel and twist interfaces add only the elementary modules in the next two rows. |
| `Topology` | `CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`, `CompactOpen.ConjugationStabilizer`, `Nonarchimedean.Subgroup` | Compact-open neighborhoods and conjugation stabilizers from locally compact nonarchimedean group topology. No representation theorem is used. |
| `Representation` | `Jacquet.PositiveCharacter`, `Twist.Definitions`, `Twist.SmoothStatement`, `Twist.SmoothProof`, `Smooth.Definitions` | Square roots and complex embeddings of positive characters; scalar twisting; open-subgroup fixed-vector definitions. Twist smoothness is proved by intersecting a fixing subgroup with the open kernel. These are lower algebraic definitions and elementary proofs, with no Jacquet functor, derivative calculation, existence or classification theorem. |
| `Representation.RankinSelberg` | `Measures`, `UnimodularityStatement`, `GeneralLinearUnimodularity` | The only declaration used by the new proof is the purely algebraic `character_eq_one`. Its proof uses only finite matrix generation and character identities. The module's additional normalized-Haar theorem uses central scalar translation, the same algebraic lemma and regular Haar uniqueness. The `Measures` import adds actual normalized general-linear and unipotent measures, rather than any Rankin–Selberg factor or classification result. |
| `Representation.Conductor` | `Congruence` | Imported through `Measures`; definitions and compact/open proofs for integral and level matrix subgroups using valuation, ideal quotients and local-field topology. It imports only Mathlib, and supplies no conductor theorem about representations. |
| `Analysis.Local` | `ModularCompactAverage` | The invoked `measure_preimage_conj` uses left invariance and the right-translation scalar, proved by `modularCharacterFun_eq_haarScalarFactor` and Haar uniqueness. Other declarations in the module prove compact averaging from actual Haar hypotheses and Fubini; they use no excluded project theorem. |

The radical input is a proved, published result. In particular,
`radicalHaar_map_leviConj` transports an arbitrary radical Haar measure through
`radicalContinuousEquiv`, makes it additive Haar in `Fin n → F.Carrier`,
applies `padicScalarHaarScaling` and `haarMeasure_map_matrix`, and pulls the
result back through a measurable embedding. This gives the inverse determinant
factor for the same supplied `T`. Its whole mathematical chain consists of
normalization, finite matrix algebra and Haar theory. The statements it imports
are proposition definitions; none is mistaken for a proved premise.

The general-linear algebraic lemma was audited at its proof body, including the
empty-index case. The full import closure through `Measures`,
`UnimodularityStatement` and `Conductor.Congruence` was checked, although the
new proof does not invoke their chosen-normalization or integral-subgroup
results. Likewise, `HaarModulus` imports elementary twist and positive-character
interfaces, but no minus-functor normalization adapter or conclusion of a later result.

The published `ParabolicModularCharacter` supplied the adapted
Haar-uniqueness and cancellation argument, and was examined for its mathematical
inputs. It is not imported. Its integral-point contraction and compact-open
radical argument are replaced here by arbitrary compact coordinate slices and
scalar `-1` conjugation. The remaining central-character extension uses the
same independently algebraic `character_eq_one` already audited above. Thus
neither that adaptation nor its new implementation uses a downstream segment
or representation-theoretic result.

The nonproject dependencies are Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435` and the pinned Lean toolchain.
The relevant measure inputs are Haar uniqueness, compact finiteness, open-set
positivity, measurable pushforward/restriction and the actual modular-character
definition; the algebra inputs are last-row determinant expansion,
diagonal/transvection induction, and finite products. No imported or
mathematically used result depends on any excluded conclusion listed below.
There is no Ze80 input, no derivative result and no classification or
exhaustion premise.

## Independence from the segment results

This is an upstream two-factor input to the segment arguments. Neither this
proof nor any prerequisite depends directly or transitively on the following
results, their mathematical conclusions or downstream consequences:

- Individual special-head/reverse-socle existence.
- Individual segment-socle/reverse-head existence.
- Analytic segment classification.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`.
- Multisegment special-head exhaustion.
- Ordered strong-head existence.
- Quotient coverage.
- Ordered conversion.
- Tempered uniqueness.
- `SquareIntegrableLanglandsClassification`.
- Square-integrable exhaustion.
- Regular exhaustion.
- Special-head product irreducibility.
- `GenericSegmentProductUniqueness`.
- `OrderedMultisegmentSocleExistence`.
- `MultisegmentSocleExhaustion`.
- `SegmentSocleProductIrreducibility`.
- Adjacent socle commutation.
- `SegmentFullJacquetFormula` and its proof.
- `SegmentHeadJacquetFormula`.
- `SegmentSocleJacquetFormula`.
- `SegmentSpecialJacquetExponentNormFormula`.

The proof also uses none of Ze80's segment derivative formulas (§3.5 or
§9.6), assumes no derivative result (including BZ77's), and assumes no
segment product irreducibility criterion (Ze80 4.2 or 9.7), no analytic or
square-integrability result (Ze80 9.3), and no classification or exhaustion
theorem. Ze80 Theorem 4.2's linked-pair converse rests on §2 and cannot
prove Proposition 1.11 circularly. These exclusions hold for every
prerequisite; the import and mathematical proof-dependency audit above
documents them. Shared lower constructions are reused only
after their independence is checked.

The proof also does not use the nonadjacent two-supercuspidal conclusion
`Langlands.Classification.TwoSupercuspidalNonadjacentProductIrreducible`
or the full two-factor
`Langlands.Classification.TwoSupercuspidalProductStructure`, their mathematical
conclusions or downstream consequences. This restriction excludes use
of their conclusions, not reuse of independently proved lower helpers.
General BZ77 infrastructure is reused only where its independence is proved.
