# An actual terminal witness for a linked pair

This internal construction supplies the segment geometry in the first paragraph
of Zelevinsky 1980, section 9.9, printed page 201. It constructs an actual
nonempty segment and its natural cut index. It does not assert an occurrence
in a representation derivative or prove a product irreducible or reducible.

## Interface and conventions

`Langlands.PadicField.TopologicalData.Segment.linkedTerminalWitness` takes an
arbitrary prime, an actual p-adic field, its supplied topological realization,
independent field and original supercuspidal carrier universes, integral twist
freeness, actual segments `Delta`, `Gamma`, `U`, an optional actual segment `I`,
and witnesses that `Delta` precedes `Gamma` and that `U,I` are their
union/intersection replacement. The returned `LinkedTerminalWitness` has:

- An actual nonempty segment `E` and a natural number `cut < Delta.length`.
- The equalities `E.base = Delta.base.twist cut` and
  `E.length + cut = Delta.length`.
- The equality `E.base = Gamma.base.twist (-1)`.
- The terminal relation `IsTerminalTruncation (some E) Delta`.
- The exact support identity
  `E.support = Delta.support intersect (Gamma.twist (-1)).support`.
- For every optional terminal truncation `A` of `U` and optional terminal
  truncation `B` of `I`, the inequality
  `E.support != optionalSupport A union optionalSupport B`.

`IsTerminalTruncationOfOptional B I` spells out the last premise: if `I` is
absent then `B` must be absent; if `I = some J`, it is the existing terminal
truncation relation for `J`. It imposes no condition on a nonexistent segment.
The new relation is a Prop-valued definition, while the witness constructor
returns actual segment data and proofs of its properties.

The segment and its cuspidal data stay in the original universe `uV`. The field
universe `uF` is independent. All input segments are actual existing objects;
no representation representatives, classification representatives, or resizing
are chosen. The constructor applies to juxtaposed linked segments, when the
intersection is absent, and to a zero cut, when `E` is the whole first segment.
There is no requirement that any outside segment family have distinct entries.

## Implemented construction

The published `IsUnionIntersectionReplacement.coordinates` supplies a common
cuspidal twist line and inclusive integral endpoints
`Delta=[a,b]`, `Gamma=[c,d]`, `U=[a,d]`, with `a<c<=b+1` and `b<d`.
Any present intersection `J` has endpoints `[c,b]`.

The constructor takes `E = ofIntegralInterval rho (c-1) b` and
`cut = (c-1-a).toNat`. The endpoint inequalities give `a<=c-1<=b`, so this
is an actual nonempty segment. The coordinate length equations give the
strict cut bound and `E.length + cut = Delta.length`. Integral-to-real casts
and the actual twist composition law give its two base equalities.

The existing support-containment comparison proves the terminal relation;
the common upper endpoint identifies the retained last member. The negative
one-twist of `Gamma` has coordinates `[c-1,d-1]`. Applying the published
support-intersection lemma identifies its intersection with `Delta` as
`[c-1,b]`. This retains equality of actual cuspidal support sets, not just
an equality of interval lengths.

Two endpoint exclusions prove the final obstruction. The union's last member
has exponent `d`, which lies outside `E` since `b<d`. The base of `E` has
exponent `c-1`, which lies outside `Gamma`. Both exclusions use the supplied
integral twist freeness. If `A=some S`, its terminal relation puts `U.last`
in `S.support`, contradicting the first exclusion under the alleged union
identity. If `A=none`, that identity puts `E.base` in `optionalSupport B`.
An absent `I` forces `B=none`, impossible. A present `I=some J` makes any
nonempty `B` lie inside `J`, hence inside `Gamma`, contradicting the second
exclusion. The empty `B` case is immediate. No multiplicity argument is
used: this is exactly the support-set obstruction required at this step.

The existential published coordinates are eliminated into `Nonempty` of the
witness type, and `Classical.choice` returns the actual witness. This choice
does not eliminate a Prop-valued existence directly into data.

## Provenance and independence

The original contextual source is A. V. Zelevinsky, *Induced representations
of reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), 165--210, registered
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The first paragraph on printed page 201 defines the distinguishing segment
as the intersection of the first segment with the negative one-twist of the
second, and says its characteristic function cannot be decomposed by
terminal truncations of the replacement union and intersection. Worker 357
read printed pages 198--201 and viewed the retained page-201 image
`.private/tmp/pdf-pages/ad6f50781a84e3a6-p38.png`. No applicable errata file
was found in the supplied public notes. The constructor is a derived actual
witness interface for that elementary geometry; it does not import the
source's segment derivative or product assertions.

The two direct imports are the published `SegmentUnionIntersection` and
`SegmentTruncationObstructionProof`. The used inputs are integral coordinates,
coordinate membership and containment, actual union/intersection replacement
coordinates, the segment last-member coordinate identity, and elementary
integer, natural-number, real-cast, twist and set reasoning. The imported
truncation-obstruction theorem is not used as a theorem; that module supplies
the published last-member coordinate lemma. Integral twist freeness remains
an explicit hypothesis of this constructor.

A complete native recursive import audit against Library commit
`146a43c03e57296c496825ab3176b07715c492b7` found 63 project modules, including
this entry, and 58 external frontier imports. All 62 inherited Lean/Markdown
pairs equal the supplied published Library. Every project module has a
nonempty paired Markdown file. There are no missing imports, proof holes,
new axioms, prohibited execution syntax, derivative modules or mirabolic
modules, and no scanned excluded conclusion. The complete inventories follow.
The used bodies of the coordinate, membership, replacement and endpoint
lemmas were read directly.

This closure uses none of the host's excluded segment, special-head, segment
socle, full Jacquet, multisegment or Langlands classification conclusions,
Ze80 3.5/9.6 or their proof successors, `SegmentHeadSupportStep`,
`SegmentHeadJacquetReduction`, or the restricted `core_mid` intermediate.
The basic segment/socle relation definitions in `Segments` assert no such
proved conclusion. No pending candidate is consumed. The six trusted operator
rulings at correspondence files `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`, `30144f6f9b59540b88b6d4c1517892d9`,
`ed80148e21e7523abfc048f455e98eb0`, `2b33898bdd0a5ff1b9031be5155a06f0`
and `ca18fd5005bf5e12a3f7cade18dca865` were read in full. This elementary
closure invokes neither the general-derivative permissions nor the support
proof's restricted reducibility exception.

The host's full `SegmentHeadProductIrreducibility` iff remains unproved.
In particular this constructor supplies no actual derivative constituent,
no nonoccurrence theorem about a smooth representation, and no isomorphism
between original and replacement products. Those require separately proved
representation-theoretic bridges. The actual derivative occurrence, when
constructed, belongs on the original linked-pair side; the present obstruction
belongs on the replacement side.

## Complete project import inventory

```text
Langlands.Combinatorics.RelationInversions
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.LeftQuotient
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.LinkedSegmentTerminalWitness
Langlands.Representation.Classification.SegmentIntegralCoordinates
Langlands.Representation.Classification.SegmentIntervalLinkage
Langlands.Representation.Classification.SegmentReplacementInversions
Langlands.Representation.Classification.SegmentTruncationObstructionProof
Langlands.Representation.Classification.SegmentTruncationObstructionStatement
Langlands.Representation.Classification.SegmentUnionIntersection
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Tensor.Finite
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
Langlands.Topology.CompactNormCharacter
```

## Complete external frontier inventory

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Group.List.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Int.Interval
Mathlib.Data.List.Pairwise
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
