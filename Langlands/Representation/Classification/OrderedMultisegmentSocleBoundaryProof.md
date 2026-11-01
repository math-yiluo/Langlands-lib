# Elementary boundary theorem for actual segment-socle products

Author: Worker 700.

`Langlands.Classification.orderedMultisegmentSocleBoundary.{uF,uV} F T`
proves exactly the target proposition
`Langlands.Classification.OrderedMultisegmentSocleBoundary.{uF,uV} F T`.
The outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with independent field and carrier universes.
The proof installs the supplied topology and gives the statement's three
conjuncts by the lemmas below. The first two conjuncts retain the saturated
carrier universe `max uF uV`; the third retains precisely its explicit
integral-twist-freeness premise at `uV`.

`orderedMultisegmentSocle_rankZero` applies to every actual
`d : T.SegmentProductDatum.{max uF uV,uF} 0` with its supplied nonprecedence
order and segment-socle blocks. It proves `d.IsZelevinskySocle d.induced`
for that same actual upper normalized product. The published
`rankZeroNormalizedProduct_isIrreducible` identifies this product with a
complex scalar line: positivity of each block degree makes the rank-zero
index set empty, the empty tensor is the scalar field, and induction from
the full trivial group preserves that carrier. The local
`irreducible_self_socle` lemma uses the identity intertwiner. Every
competing injective map from an irreducible representation is nonzero,
hence surjective by irreducibility of the ambient representation. Its
range and the identity's range are both the full space. Thus the proof
supplies the strong subobject relation, including an injection and equality
of images for every competing irreducible embedding; the empty datum is
included.

`segmentSocleProduct_nontrivial` applies in every rank and requires only
the actual `HasSegmentSocles` hypothesis. Each supplied block is
irreducible by its socle relation, so its complex vector-space basis has a
nonempty index type. The tensor product of these bases has a nonzero basis
vector, also for an empty family. The actual normalized inducing
representation is smooth by external-tensor smoothness, continuous
pullback along the Levi projection, and the open-kernel half-modulus twist
law. The compact local section construction supplies a smooth induced
function with any prescribed tensor value at the identity. Evaluation is
therefore surjective. A function evaluating to the chosen nonzero tensor
is nonzero, proving `Nontrivial d.induced`. No ordering hypothesis enters
this conjunct.

`precedenceOrdered_endpointSeparated` works for every finite actual
segment family at carrier universe `uV`, including repeated segments and
the empty family. It assumes exactly
`CuspidalIntegralTwistFreeness.{uF,uV} F T`. If a later base equals the
one-step twist of the earlier last element, the local
`segmentPrecedes_of_endpoint_eq` gives integral coordinates
`[0,m-1]` and `[m,m+l-1]` for the two segments, where `m,l` are their
positive lengths. The published interval-precedence criterion, with the
explicit freeness premise, then gives earlier-to-later precedence. This
contradicts the supplied nonprecedence ordering. The proof establishes
no analytic freeness theorem.

These are internal lower consequences of the actual Library
constructions. The source context is A. V. Zelevinsky, *Induced
representations of reductive p-adic groups II. On irreducible
representations of GL(n)* (1980), literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Section 4.1, printed p.184 / one-based PDF21, defines precedence;
Theorems 6.1(a) and 6.2, printed p.188 / PDF25, explain the parent
ordered-socle assertion and its endpoint condition. These passages were
read in the registered original and the formula pages were visually
checked. The retained full PDF hash matches registration. Bounded searches
of the prescribed errata locations, literature index and relevant source
notes found no applicable correction. The three-conjunct grouping is an
internal formulation, and this proof follows the elementary constructions
just described rather than asserting the full positive-rank source
result. It proves no positive-rank ordered-socle existence, finite length,
homogeneity or highest-derivative formula.

The rank-zero dependency in
`Langlands.Representation.Classification.OrderedMultisegmentHeadReduction`
is confined to `rankZeroNormalizedProduct_isIrreducible`,
`rankZeroNormalizedProductLinearEquiv` and the scalar-line irreducibility
lemma. Their implementation uses empty block indices,
`Induction.smoothInducedTopEquiv`, `PiTensorProduct.isEmptyEquiv` and the
simple-module lattice of the complex scalar line. The conditional
head-assembly lemmas elsewhere in that imported module are unused.
Product nonzeroness uses actual compact open subgroups, smooth tensors,
continuous pullback, the open-kernel half-modulus law and
`Induction.compactLocalSection_apply`. Endpoint separation adds only the
integral-coordinate and interval criteria with their explicit freeness
premise. The imported scalar norm identity in `SupercuspidalTwist` uses
determinant normalization and real-power arithmetic.

The complete project import closure and its comparison with the Library
are recorded below. The closure contains classification proposition
definitions imported by the existing target statement. Defining those
propositions proves none of them. The implemented proof uses no socle
exhaustion, analytic segment classification, special-head existence or
exhaustion, quotient coverage, tempered uniqueness, square-integrable or
regular exhaustion, segment-product irreducibility criterion, conditional
head-assembly conclusion or other excluded downstream result. It uses no
derivative, induced-product finite length, Artinianity, homogeneity or
analytic strong-indecomposability input. The target statement pair and its
imports remain unchanged.

The current import audit uses Library commit
`46311733bb8c7e91d5c932b568a8f16981d98999`, which is also the refreshed
workspace base, with no refresh conflicts. All 87 dependency pairs,
including the independently reviewed and published target statement,
match that tree byte for byte; none is missing or unpaired. The statement
and every imported pair are unchanged. Relative to the previous helper audit,
`NormalizedCharacter` now imports `Topology.CompactNormCharacter`; its new
compact-subgroup lemma applies the elementary theorem that a continuous
positive character is trivial on a compact subgroup. That theorem bounds
powers in a compact real image and then applies the same bound to inverses.
The normalized determinant construction and the open-kernel proof used
here are unchanged. The earlier move of the unchanged
`Jacquet.twist_comp_subtype` into `Jacquet.CharacterTwistEquiv` was also
checked; that module contains only algebraic quotient/twist identifications.
These changes introduce no classification input.

The complete 87-module project dependency list is:

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.Maps
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.MultisegmentClassificationStatement
Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryStatement
Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionStatement
Langlands.Representation.Classification.RegularLanglandsStatement
Langlands.Representation.Classification.SegmentIntegralCoordinates
Langlands.Representation.Classification.SegmentIntervalLinkage
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedBlockStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
```

Development check `35fc1c61-b3f3-4e97-8b00-83e4ff655e40` completes a Lake
build and declaration inspection with zero errors or warnings. It confirms
a theorem with independent `uF,uV` and only `propext`, `Classical.choice`
and `Quot.sound`. This development result is distinct from independent
semantic acceptance and the staged exact-target proof validation.
