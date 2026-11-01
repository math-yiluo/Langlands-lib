# Haar character on the actual left-Phi stages

Author: Worker 499.

This derived module proves `leftPhiStagesHaarRatio_eq_one`: the actual
intersection-to-kernel Haar character of the restricted left stages
retraction is the constant character `1`, at both actual orbit
representatives. It uses the published actual matrix subgroups and
retraction. Its p-adic adapter proves this identity for every supplied
topology, deriving the needed local compactness.
The normalized representation comparison and the final six-part host
theorem remain separate obligations.

## Source and provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8, printed pp.444–445 (one-based PDF pages 5–6), gives
character localization and its normalizing-subgroup action. Sections
3.1–3.2, printed pp.450–451 (PDF pages 11–12), give the mirabolic
character and minus functors. Section 4.12(II), printed pp.456–457
(PDF pages 17–18), defines the left mixed product; §4.13(b),
printed p.458 (PDF page 19), gives its functorial comparisons.
Section 7.2, printed p.471 (PDF page 32), gives the two left orbit
representatives. These passages and relevant page images were read
during this task. The bounded supplied-source and public-note errata
search found no applicable BZ77 entry; no global absence is asserted.

This module and `SplitKernelHaarTrivial` are internally derived
content. The original motivates the eventual p-adic application; it
does not literally state the arbitrary-ring kernel lemmas or the
abstract full-intersection Haar identity. The proof uses the actual
published matrix groups, restricted retraction, Haar ratio and
continuous-conjugacy theorem. No source comparison or pending
comparison is assumed. Worker 499 wrote these two pairs; no peer
draft contributes a proof body.

## Parameters and actual groups

The algebraic results quantify every `R : Type uR` with `[CommRing R]`,
every `k,r : ℕ` including zero, and every `i : Fin 2`. Write

```text
G   = plusSubgroup (k+r+1) R,
L   = mirabolic (k+r+1) R,
p   = plusProjection : G ->* L,
s   = plusSuccessor : L ->* G,
P_i = leftStages k r R i,
H_i = leftStabilizer k r R i,
K_i = P_i.comap s,
H'_i = H_i.subgroupOf P_i,
r_i = leftPhiHaarRetraction : P_i ->* K_i,
s_i = s.subgroupComap P_i : K_i ->* P_i.
```

The ambient mirabolic group is
`mirabolic (k+r+2) R = P_(k+r+3)(R)` and `L = P_(k+r+2)(R)`.
The eventual GL factor has positive rank `k+1`; the source mirabolic
factor for Phi-minus is `mirabolic (r+1) R = P_(r+2)(R)`.
The host convention `phiMinus T ψ r : P_(r+2) -> P_(r+1)` is retained.
No `P_0` or Phi-minus on `P_1` is introduced. The representative index
`0` is the descending cycle and `1` is the identity.

The topological character identity uses a Hausdorff topological ring,
local compactness of `ker r_i`, and Borel measurable structures on
`ker r_i` and `H'_i.comap (ker r_i).subtype`. These are exactly the
structures needed to form the existing Haar character. Its codomain
is the group of units of `ℝ≥0`; equality to `1` means equality of
monoid homomorphisms on the whole actual group `K_i`.

## Implemented proof

The proof first uses `leftRadicalIntersection_eq_top` to put every
plus-projection kernel element in the actual left stabilizer. The
kernel equation is converted to actual radical membership using
`projection_eq_one_iff`. The published stabilizer-to-stages inclusion
gives the kernel containment needed by `splitStagesRetraction`.
Removing the intermediate subgroup membership shows that the nested
kernel lies in the nested stabilizer as well.

Section containment is proved only for the actual section preimage
`(leftStages k r R i).comap plusSuccessor`. Its membership equation
reduces by `plusProjection_plusSuccessor` to membership in the lower
section. The nested stabilizer is closed because its underlying
stabilizer is closed and the subgroup inclusion is continuous.
The general `splitKernelHaarRatio_eq_one_of_ker_le` then identifies the
intersection conjugation and kernel conjugation through the continuous
equivalence that forgets the redundant membership. Their actual Haar
scaling factors agree, so the exact ratio is one.

More explicitly, the helper `splitKernelFullIntersectionEquiv`
identifies `H.comap r.ker.subtype` with `r.ker` whenever `r.ker ≤ H`.
It forgets the redundant membership proof; its inverse reinserts that
proof. Both maps are continuous and retain the same kernel element.
They intertwine inverse section conjugation and its intersection
restriction by definitional equality. The published
`Langlands.Geometric.haarChar_eq_of_conjugacy` therefore equates the
numerator and denominator of `splitKernelHaarRatio`; positivity makes
the denominator nonzero, and division gives `1`. This calculation
uses the actual intersection-to-kernel ratio with its existing
orientation. It assumes neither a trivial kernel nor a compact kernel.

`leftPhiHaar_kernel_isClosed` takes the preimage of the closed
identity singleton under the continuous restricted retraction. It
needs a topology and Hausdorff property on `R`; the topological-ring
assumption is omitted for this declaration.
`leftPhiHaar_kernel_locallyCompact` starts with local compactness of
`GeneralLinear (k+r+3) R`, then uses the closed mirabolic, plus,
stages and kernel subgroups in that order. The stages and stabilizer
closedness results use the Hausdorff topological-ring structures.

Finally `padic_leftPhiStagesHaarRatio_eq_one` quantifies arbitrary
`{p₀ : ℕ} [Fact p₀.Prime]`, `F : PadicField.{uR} p₀` and
`T : F.TopologicalData`. It installs precisely `T.topology`,
`T.fieldT2`, the topological-ring structure derived from `T`, and
`T.generalLinearLocallyCompactSpace (k+r+3)`. It derives local
compactness of the actual nested kernel, assigns the Borel
measurable structures to the actual kernel and intersection, and
applies the preceding exact ratio identity. These structures appear
as explicit `letI` binders in the theorem statement. No further
local-compactness, scalar-identity or representation-comparison
premise is added. The coefficient field, representation carrier,
additive character and representation are absent from this
group-theoretic computation.

## Import and mathematical dependency audit

The four direct project imports are `SplitKernelHaarTrivial`,
`SplitStagesRetraction`, `MirabolicMixedOrbitStages` and
`MirabolicMixedOrbitRadicals`, with their full names below.
The complete closure excluding the entry has 86 project modules:
the new helper and 85 published imports. All 170 files in those
published Lean/Markdown pairs are nonempty and byte-identical to
the Library and manifest at commit
`a8934c89b9ba4ec0a4ce1a27cee0290064384404`.
The helper is submitted with this pair and is not a pending input.
There are no pending imported modules.

The actual mathematical inputs are the mirabolic projection and
successor, the actual left stabilizer/stages inclusions, the proof
that the left radical intersection is the whole radical, the
restricted split-retraction construction and its continuity,
closed matrix subgroups, closed subspaces of locally compact
spaces, the supplied p-adic general-linear local compactness,
the explicit Haar-ratio definition, restriction of section
conjugation, continuous-conjugacy invariance of Haar scaling,
and positivity of Haar scaling. These reduce to actual matrix
entries, subgroup membership, continuity, closedness and Haar
measure uniqueness.

`SplitKernelEquivariant` defines the existing Haar character and
also imports ordinary compact-induction and quotient-integral
theory. No comparison theorem from that theory is invoked by
this unit. Its transitive smoothness, category, induction,
quotient measure and tensor modules remain unchanged. No
character compact-induction comparison or mixed-minus
comparison is inferred from their proposition definitions.

| Condition | Actual dependency finding |
| --- | --- |
| Six host mixed-minus conclusions | No host comparison or boundary conclusion is used. Only the actual full-kernel containment, closedness, local compactness and Haar-ratio calculation are proved; the final natural isomorphisms, exact sequence and conjunction remain obligations. |
| Plus functors, adjunction, BZ77 §4.13(d) | No plus functor, adjunction or submodule-detection result supplies an input. The permitted elementary matrix subgroup `plusSubgroup` and its projection/section are used explicitly. |
| General Leibniz and derivative formulas | No general Leibniz proof, segment derivative formula, Ze80 §3.5 or §9.6 formula, or unproved BZ77 derivative result supplies an input. |
| Segment head, socle and Jacquet formulas | No individual special-head or segment-socle existence, linked/unlinked or juxtaposed reverse-product conclusion, quotient homomorphism, or full/head/socle/special Jacquet formula supplies an input. |
| Product, commutation and gluing consumers | No segment product irreducibility, adjacent swap, two-segment commutation, linked-segment gluing, or Ze80 4.2 or 9.7 criterion is used. |
| Special-head criterion and generic uniqueness | Neither the special-head product criterion nor generic segment-product uniqueness is used. |
| Ordered existence and exhaustion | No ordered multisegment-socle existence, socle or special-head exhaustion, ordered strong-head existence, quotient coverage or ordered conversion supplies an input. |
| Analytic, tempered, square-integrable conclusions | No segment classification, forward special essential square-integrability, tempered uniqueness, square-integrable classification or exhaustion, regular exhaustion, or Ze80 9.3 assertion supplies an input. |
| Two-supercuspidal consumers | Neither nonadjacent product irreducibility, product structure nor full-product assembly is used. No parent six-statement conclusion (b),(d),(e),(f) supplies an input. |
| Supercuspidal and single-block finiteness | No supercuspidal coinvariant-finiteness statement, all-character single-block conclusion, arbitrary-character finiteness theorem or consequence supplies an input. |
| Other Whittaker finiteness | No irreducible or Levi-cuspidal finiteness conclusion, consequence or prohibited mirabolic finite-length route supplies an input. |
| Generality | All natural k,r including zero and both actual representatives are retained. The p-adic theorem uses every supplied T. The generic helper has independent group universes; no representation carrier, nonzero vector, admissibility, finite dimension, finite length, genericity, canonical topology, universe saturation or theorem-valued comparison premise is introduced. |
| Published inputs and target preservation | Every published imported pair is unchanged. The new helper accompanies the entry. Pending statements, drafts, source formulas and citations are not theorem premises. No host statement or any pair it imports is modified. |
| Separate owners and user controls | This focused unit does not construct a restriction sequence, exactness proof or generic compact-induction comparison. Worker 127's operator pause, Worker 8's suspension, Worker 114's hold and all current suspensions remain binding. |

A source scan of both new modules and the complete project closure
finds no occurrence in Lean code of the host's 38 excluded task
identifiers or 24 named consumer declarations, and no proof holes,
new axioms or unsafe evaluation commands. This supplements the
condition-by-condition mathematical dependency audit. Compilation
and declaration inspection are development checks; independent
acceptance and publication remain required.

## Complete project import closure

Both direct roots and every transitive project import are included
below, excluding the present entry. `SplitKernelHaarTrivial` is the
new helper included in this candidate. Mathlib is supplied by the
pinned environment and remains unchanged.

```text
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.UpperUnipotent
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelHaarTrivial
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
