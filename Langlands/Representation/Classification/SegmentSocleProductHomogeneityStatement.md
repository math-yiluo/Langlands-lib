# Homogeneity of endpoint-separated segment-socle products

Authors: Worker 700 and Worker 999.

`Langlands.Classification.SegmentSocleProductHomogeneity F T` is a
proposition definition for every prime, supplied p-adic field `F`, and
compatible topology datum `T`. It retains independent field and
cuspidal-carrier universes `uF` and `uV` and installs the supplied topology.
For every nontrivial unitary additive character `ψ`, every natural `N`,
and every actual `d : T.SegmentProductDatum.{uV,uF} (N+1)`, it asserts
homogeneity of `d.induced` provided that its actual blocks are segment
socles and the following endpoint condition holds:

```lean
∀ i j : Fin d.length, i < j →
  (d.segments j).base ≠ ((d.segments i).last).twist 1
```

The condition concerns the beginning of the later segment and the
one-step integral twist of the end of the earlier segment. The exponent
`1` is the factor usually denoted `ν` in the source. The indices and the
two endpoints have this precise direction. The statement does not demand
full nonprecedence order or pairwise nonlinkage. It permits repeated
entries whenever the displayed condition holds.

The datum fixes the actual block representations, their multiplicities
and their order, and `d.induced` is their actual normalized upper
parabolic product with right translation. Its carrier universe is the
existing `max uF uV`. `d.HasSegmentSocles` refers to the existing strong
segment-socle relation on each supplied block. The proposition never
reorders, replaces or constructs these blocks.

`Derivative.IsGeneralLinearHomogeneous T ψ d.induced` means that the actual
restriction of this product to `GeneralLinear.mirabolic N F.Carrier`
is homogeneous. This subgroup is the source's `P_(N+1)`. Homogeneity
uses the actual invariant subspaces with their restricted smooth actions:
each nonbottom subrepresentation has the ambient representation's
derivative level. Level is the greatest nontrivial positive-order
derivative, totalized to zero when all valid derivatives are zero.

All positive general-linear ranks are covered. In particular `N=0`
means `GL_1` restricted to `P_1`; the only valid positive derivative order
there is one, with target `GL_0`. This proposition makes no homogeneity
assertion for `GL_0`. The separate ordered-socle argument handles
rank zero and its empty datum directly.

The original source is Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), registered as
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Sections 5.1 and 5.2, printed p.187 / one-based PDF page 24, define
mirabolic homogeneity and general-linear homogeneity by restriction.
Theorem 6.2, printed p.188 / PDF page 25, has exactly the endpoint
condition and homogeneity conclusion recorded here. Section 6.3, printed
pp.188–189 / PDF pages 25–26, explains the proof modifications.

The lower source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Zelevinsky's section 6.3 adapts the two-case argument in BZ77 section
4.15, printed pp.458–459 / PDF pages 19–20, using derivatives of
segment socles and mixed mirabolic product and restriction filtrations.
The product inputs occur in BZ77 sections 4.11–4.14; sections 4.13 and
4.14 are on printed p.458 / PDF page 19.

The other lower ingredients are Ze80 section 5.3 and the support
reasoning in section 4.5, printed p.185 / PDF page 22. The latter uses
the support bookkeeping of section 4.4 on that page, the segment
derivative calculation of section 3.5, printed p.182 / PDF page 19,
and BZ77 sections 4.6 and 4.7(b), printed p.455 / PDF page 16, on
derivatives of products and shifted support. This route is independent
of the subsequent linked-pair theorem in Ze80 section 4.6, the final
unlinked-product irreducibility criterion, and classification. It also
precedes the derivation of section 6.1(a); the ordered-socle conclusion
of that derivation is not an input here. All these analytic lower
ingredients remain future proof obligations. No errata note for either
source exists in the Library notes (there is no `notes/errata` directory)
or in the project literature index, and the rendered source pages show no
applicable correction.

The imported derivative normalization uses explicit determinant
absolute-value twists with exponent `-1/2`; comparison with the source
Haar-modulus normalization remains a separate obligation. This module
supplies no homogeneity proof, derivative calculation, filtration,
commutation, finite-length theorem, irreducibility criterion or
classification theorem. Its only premises are the supplied segment-socle
relations and the displayed endpoint condition.

The only direct project imports are the published modules
`Langlands.Representation.Derivative.Homogeneity` and
`Langlands.Representation.Classification.LanglandsData`.
The complete transitive project import closure was traversed and checked against Library commit `3987c3d7445531c2c7f784464a3fd47061ba0865`. Every dependency Lean/Markdown pair is byte-identical to that published tree; no project import is missing and every dependency is paired.

The closure has 78 project modules, listed completely below. The derivative branch contains actual quotient/functor constructions, rank transport and the level/homogeneity definitions. The product branch contains actual parabolic induction and segment data; its Essential and Tempered modules supply definitions, not classification conclusions. No ordered-socle, socle exhaustion, segment-classification, product irreducibility, segment commutation, special-head existence/exhaustion, quotient coverage or uniqueness theorem is imported. The scalar norm formula in SupercuspidalTwist was checked directly: it expands the real-power character and determinant norm of a scalar matrix and uses real-power arithmetic only. Its original placement in a linked-head module supplies no proof dependency here. SupercuspidalTwist now imports `Langlands.Representation.Jacquet.CharacterTwistEquiv`, which received the unchanged theorem `twist_comp_subtype`; that module imports only Jacquet coinvariants and twist definitions and supplies elementary identifications of actual coinvariant quotients before and after a character twist trivial on the radical. `Twist.ContinuousCharacterProof` gained only an elementary local-constancy lemma for continuous complex characters.

The published Homogeneity pair was independently accepted and was verified byte-for-byte before this statement was authored. All transitive imports are lower constructions or elementary laws. The source proof dependencies described above are obligations of later proof tasks, not hidden hypotheses or claims of this proposition definition. The full task exclusion set also applies to every later proof split.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
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
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
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
Langlands.Topology.Nonarchimedean.Subgroup
```

Development check `e47cf7b2-8305-4968-acad-3707955f01d1` of this workspace pair in approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` succeeded with zero errors or warnings, `statement_returns_prop: true`, exactly the independent universe parameters `uF` and `uV`, and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. A separate private check `4244b2ae-cd06-4f5d-9d90-7632cb36b92e` confirmed by `Iff.rfl` that the definition unfolds to the fully explicit form with `Segment.base`, `CuspidalDatum.twist (1 : ℝ)` applied to the member of index `length - 1`, and `IsHomogeneous` of the actual restriction `(generalLinearRestriction N).obj` of `d.induced`. These development results establish elaboration and proposition kind; independent semantic review and publication are still required. No proof of the proposition is supplied.
