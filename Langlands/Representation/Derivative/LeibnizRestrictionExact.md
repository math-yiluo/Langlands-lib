# The actual differentiated product restriction sequence

Author: Worker 593.

This derived helper constructs a natural short exact sequence whose middle
functor is the unchanged `leibnizSource`. The subobject is the actual right
mixed derivative source precomposed by restriction on the first input. The
quotient is the actual restriction quotient followed by the actual derivative.
It supplies a focused step toward the positive-rank, positive-order Leibniz
argument. The full mixed derivative comparisons and the construction of the
Leibniz filtration remain separate obligations.

## Parameters and declarations

Let `F : PadicField.{uF} p`, `[Fact p.Prime]`, and let
`T : F.TopologicalData` be supplied. The input carrier universe `uV` is
independent of `uF`. The parameter `ψ` is the bundled continuous nontrivial
unitary additive character. Write `a=m+1`, `b=n+1` and `N=m+n+1`.
The input category consists of pairs of arbitrary smooth complex
representations of `GL_a(F)` and `GL_b(F)`, with carriers in `uV`.
The precise order hypothesis is `0 < d ∧ d ≤ a+b`. All three output functors
land in `Rep.{max uF uV} ℂ (GeneralLinear (a+b-d) F.Carrier)`.

`leibnizRestrictionDerivativeSubobject` is the composite

```text
(generalLinearRestriction T m).prod (identity on SmoothRep GL_b)
  ⋙ rightMixedDerivativeSource T ψ b m d
  ⋙ generalLinearRepRankCast (((b+m)+1-d) = a+b-d).
```

The arithmetic witnesses are proved internally. This functor retains the
order of both inputs in the published right mixed product, including its
case (III) epsilon character. The output transport is expressed in `Rep`
for this interface. The proved equation `generalLinearRankCast_toRep`
identifies it with smooth rank transport before forgetting.

`leibnizRestrictionDerivativeQuotient` is the composite

```text
restrictionQuotient T m n
  ⋙ mirabolicDerivativeOfOrder T ψ N d
  ⋙ generalLinearRankCast T (N+1-d = a+b-d)
  ⋙ SmoothRep.toRep.
```

Here `restrictionQuotient` is exactly the published left mixed product with
restriction on the second input and its prescribed ambient rank transport.
No assertion identifying its derivative with a graded piece is used or
proved here.

`leibnizRestrictionDerivativeExact` supplies natural transformations

```text
leibnizRestrictionDerivativeSubobject T ψ m n d hd
  -- i --> leibnizSource T ψ a b d hd.2
  -- q --> leibnizRestrictionDerivativeQuotient T ψ m n d hd
```

such that, on every pair `X`, the underlying map `i.app X` is injective,
its linear range equals the kernel of `q.app X`, and `q.app X` is
surjective. These are natural arrows between the entire functors, rather
than independently chosen exact sequences on objects. Their existence is
unconditional apart from the displayed rank and order bounds: there is no
restriction, exactness or filtration proposition among the hypotheses.

The scope includes `m=0`, `n=0` and the top order `d=a+b`, whose actual
output is a representation of `GL_0` with its actual derivative carrier.
The positive inputs can restrict to `P_1`; no `P_0` is introduced.
Rank-zero input factors and order zero are outside this helper's displayed
domain and are treated by the separate boundary helpers. This module adds
no admissibility, irreducibility, finite dimension, finite length,
genericity, chosen-vector, canonical-topology or universe-equality premise.

## Implemented proof

The private `order_mapsShortExact` proves exactness of the actual
`mirabolicDerivativeOfOrder`. By its construction, this functor is an
equality-based mirabolic rank cast followed by
`mirabolicDerivative T ψ (N+1-d) (d-1)`. Eliminating the equality in a
mirabolic rank cast gives the identity functor, which preserves short exact
sequences by `LevelCalculus.mapsShortExact_id`. The unconditional published
`mirabolicDerivative_mapsShortExact` proves exactness of the second factor.
`LevelCalculus.mapsShortExact_comp` combines them. These two generic laws
come from `ShortExactFunctorLaws`, imported by the derivative-exactness
proof; the separate `LevelCalculus` module is not imported.

For the main theorem, set

```text
J = mirabolicDerivativeOfOrder T ψ N d
      ⋙ generalLinearRankCast T (N+1-d = a+b-d).
```

Apply the preceding result at carrier universe `max uF uV`, and compose
with `generalLinearRankCast_mapsShortExact`, to obtain `hJ` for this actual
smooth functor. Obtain natural arrows and objectwise short exactness from
the unconditional published `mirabolicProductRestriction F T m n`.
Whisker these arrows by `J ⋙ SmoothRep.toRep`, producing `iD` and `qD`.
The underlying maps after forgetting are the same maps whose exactness
`hJ` supplies.

The published source comparisons give natural isomorphisms

```text
eL : restrictionSubobject T m n ⋙ J ⋙ SmoothRep.toRep
       ≅ leibnizRestrictionDerivativeSubobject T ψ m n d hd
eM : restrictedProduct T m n ⋙ J ⋙ SmoothRep.toRep
       ≅ leibnizSource T ψ a b d hd.2.
```

Functor associativity and `generalLinearRankCast_toRep` put their sources
in the form needed by `leibnizRestrictionSubobjectSourceIso` and
`leibnizRestrictedProductSourceIso`. The desired natural arrows are
`eL.inv ≫ iD ≫ eM.hom` and `eM.inv ≫ qD`. On each input, convert `eL.symm`
and `eM` to representation equivalences and then linear equivalences.
`MirabolicProductRestriction.exact_of_linearEquiv` transfers injectivity,
range-kernel exactness and surjectivity through these equivalences; the
quotient uses the identity equivalence. This finishes the displayed
existence theorem. Every source comparison, cast and arrow is natural in
both inputs.

## Source correspondence and provenance

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages are Proposition 3.2(a), printed pp.450–451
(one-based PDF pp.11–12), the derivative definitions in §3.5, printed p.452
(PDF p.13), and §4.3, printed p.454 (PDF p.15), and Proposition 4.13(a)
and Corollary 4.14(c), printed p.458 (PDF p.19).
The source restriction sequence has the right mixed term as subobject and
the left mixed term as quotient, and is functorial. The proof of 4.14(c)
uses this sequence together with the two mixed derivative assertions.
The source's positive-rank `P_s` corresponds to
`GeneralLinear.mirabolic (s-1) F.Carrier`.

This module derives only the exact sequence after applying the actual
positive derivative. Its mathematical inputs are the independently
published proofs of the restriction sequence and minus/derivative
exactness, rather than the printed assertions as unproved hypotheses.
The source does not name this precise Lean interface: the two source
functors, equality-based rank transports, forgetting and the existential
packaging of natural arrows are internal constructions. The grade
comparisons and splicing needed for 4.14(c) are not part of this result.
The determinant normalization of the minus functors and the binary and
mixed induction characters are retained by using the actual published
functors. No residual twist is canceled by assumption.

A bounded source-specific check found no registered errata file
`notes/errata/bernstein-zelevinsky-1977-induced-i.md` in the project or
current Library, and no relevant errata entry in the central-library
pointer index or source-specific errata filename in the declared reading
locations. This is a record of the local check, not a global absence claim.

## Mathematical dependency audit

The exactness branch uses the published
`GeneralLinearDerivativeExactnessProof`, whose iterate proof applies
`Mirabolic.minusExactness` from `MirabolicMinusExactnessProof` to the
normalized `Ψ⁻` and `Φ⁻` functors. That proof uses actual character
localization quotients along the closed mirabolic radical, its continuous
characters, and compact containment for the upper unipotent group.
`Jacquet.LocalizationExactnessProof` detects a finite relation span in a
compact subgroup, twists by the inverse character, and applies
`Jacquet.ExactProof`. The latter proves injectivity by finite compact-orbit
averaging; quotient span algebra proves middle exactness and surjectivity.
`Compact.Definitions` obtains finite orbits from smooth stabilizers and
compactness, and `Compact.FiniteMean` proves their averaging laws by finite
sums and equal-sized fibers. No finite-dimensionality or finite-length
hypothesis is used. `UpperUnipotentCompactContainmentProof` obtains compact
containment from the explicit upper-triangular coordinates and common
denominators. These are the actual lower mathematical inputs, not an
assumed exactness proposition or a consumer theorem.

The restriction branch uses `MirabolicProductRestriction` and its six
focused helpers. The actual two-orbit geometry, stabilizer identifications,
coefficient factors and transports give the natural open-orbit inclusion
and closed-orbit restriction. The general
`Geometric.closedSubgroupMackeyFiltration` and its assembly identify the
actual support-step kernels and their quotients.
`OrbitSectionExtensionProof` supplies closed-orbit extension by finite
clopen compact-section gluing. `Parabolic.parabolicQuotientCompact` follows
from the integral compact subgroup and `Whittaker.Iwasawa`;
`Induction.compactInclusion_bijective_of_compactSpace` then identifies
compact and smooth induction, using closed projected support. No induction
admissibility result in the same module is needed. Naturality and exactness
come from these actual function-space maps and linear identifications.

The inherited restriction closure contains three `Classification`
modules: `Supercuspidal`, `SupercuspidalContragredientStatement` and
`SupercuspidalContragredientAux`. They enter through
`Smooth.SmallRealizationProof` and `Group.GL.CountabilityProof`.
The countability certificate actually used is
`T.generalLinearSecondCountableTopology`, proved from finite matrix
products, the opposite topology and the embedding of units; sigma
compactness follows from local compactness and second countability.
No irreducible-realization or supercuspidal theorem is needed for that
certificate. The imported auxiliary module proves elementary dual,
quotient-conjugation and representation-equivalence facts and no excluded
classification or exhaustion conclusion. The presence of these module
names therefore does not supply a classification input.

The restriction orbit and coefficient helpers also inherit imports of
`Derivative.MinusVanishing` and `Group.GL.MirabolicModularCharacterProof`.
The declarations actually used there are only
`exists_lastRow_eq_of_ne_zero` and `Mirabolic.determinant_projection`:
respectively row replacement/permutation and determinant expansion.
The accompanying vanishing, Haar, Rankin–Selberg and conductor modules
supply no consumer finiteness or classification conclusion to the proof.
On the exactness branch the Haar-invariance input is the general
upper-unipotent translation/coordinate calculation, not a Whittaker
finiteness or a segment input.

The source-comparison branch uses only the defining positive derivative
comparison, equality rank transport and its composition/forgetting laws,
functor products and whiskering, proof irrelevance and natural-number
arithmetic, as documented in `LeibnizRestrictionCompat`. The imported
Leibniz and right-mixed proposition definitions only name actual source
functors. No conditional filtration extractor is applied. The generic
linear exactness transport is proved in `MirabolicProductRestriction`
from the displayed linear equivalences, with no representation theorem
among its premises.

| Inherited condition or exclusion | Check for this pair and its mathematical inputs |
| --- | --- |
| Actual natural functors, unchanged target, complete feasible indices, smooth casts and no residual twist | The middle is literally `leibnizSource`. The two arrows are natural. The subobject cast agrees with the prescribed smooth cast by the forgetting square. No target or imported pair is edited; no filtration or enumeration is asserted by this helper. The actual normalized characters remain present. |
| Supplied topology and character, independent universes, arbitrary carriers and all boundaries | `T`, `ψ`, `uF` and `uV` are unchanged parameters. There is no representation hypothesis. Positive input ranks and order are explicit scope bounds. The top order and its actual `GL_0` output carrier are included. Zero-factor and order-zero cases remain in the separate boundary results. |
| Only independently proved and published general inputs; no unproved consumer hypothesis | The proof uses the published restriction sequence and unconditional actual derivative exactness, source comparisons and elementary linear algebra. Neither a source citation nor a statement definition, draft, pending proof, mixed theorem or Leibniz assembly supplies a proof. |
| All segment derivative formulas, individual special-head/reverse-socle or segment-socle/reverse-head existence, full/head/socle Jacquet and special-exponent formulas, analytic segment classification | No segment module occurs in the complete Lean closure. No formula or existence/classification conclusion in these families is used. In particular none of the other clauses of the parent six-statement segment contribution supplies an input. |
| Unlinked/linked/juxtaposed segment structures, pair reducibility, reverse quotient maps, segment-socle product irreducibility, adjacent swaps, two-segment commutation, linked gluing, ordered socle existence and socle exhaustion | No such consumer declaration occurs in the closure or the proof route. Their conclusions, successors and downstream consequences supply no premise. |
| Special-head product criterion, generic segment-product uniqueness, multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | None enters the restriction, averaging, localization, cast or source-comparison argument. The incidental supercuspidal-definition/contragredient imports above prove no such conclusion and are not used as classification evidence. |
| Square-integrable Langlands classification, square-integrable and regular exhaustion, forward special essential square-integrability | No square-integrable or exhaustion theorem is imported or used. The proof operates on arbitrary smooth objects and their actual function spaces and character quotients. |
| Two-supercuspidal nonadjacent irreducibility, full-product structure or assembly and their downstream conclusions | None is in the closure or proof route. General exactness and general restriction are the upstream inputs used here. |
| Ze80 §3.5/§9.6 segment derivatives, 4.2/9.7 criteria, 9.3 analytic or square-integrability results, classification or exhaustion | No Ze80 result supplies a proof input. The original-source route is the general BZ77 restriction and minus-exactness construction, independently proved in the Library. |
| Irreducible, Levi-cuspidal, supercuspidal, all-character single-block Whittaker coinvariant finiteness and the dependent mirabolic finite-length route | None of the three prohibited finiteness declarations or tasks occurs in the closure. No finite-length theorem is used. Algebraic Whittaker characters and Iwasawa compactness are independent lower constructions; the incidental Rankin–Selberg imports above do not supply finiteness. |
| Operator pause and upstream/downstream ownership | No contact or wake of Worker 127 is needed or made. The accepted/public minus-exactness theorem is read and imported. This helper does not duplicate either separately owned full mixed derivative proof or claim the parent theorem. |

A recursive scan checked all excluded declaration names and all 38 unique
inherited excluded task identifiers, with no Lean-source matches in the
closure. This supplements the mathematical trace above; it does not replace
that trace or independent review.

## Complete project import closure

The three direct imports are
`Langlands.Representation.Derivative.LeibnizRestrictionCompat`,
`Langlands.Representation.Derivative.MirabolicProductRestriction` and
`Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof`.
There is no direct Mathlib import. At Library base
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb`, the recursive project closure
contains 179 modules including this entry. All 178 dependency Lean/Markdown
pairs are nonempty and byte-identical to that published base; no private
or unpublished dependency is required. The inventory, including the entry,
is:

```text
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientTopology
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeibnizIndices
Langlands.Representation.Derivative.LeibnizPieceCompat
Langlands.Representation.Derivative.LeibnizRestrictionCompat
Langlands.Representation.Derivative.LeibnizRestrictionExact
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicProductRestriction
Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.RankCastCompat
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
