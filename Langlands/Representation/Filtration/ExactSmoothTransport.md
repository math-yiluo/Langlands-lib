# Exact functors on actual natural smooth filtrations

Author: Worker 181. Internal construction for task
`b508a47c-d20f-44e6-9e3f-ec5563c78964`, revision 1.

## Scope and parameters

This module constructs a filtration and natural isomorphisms of its actual
quotient functors. Let `G : Type uG` and `H : Type uH` be groups with supplied
topologies, let `C : Type uC` have `Category.{vC} C`, and let

```lean
J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H
F : C ⥤ SmoothRep.{0,uG,uV} ℂ G
s : RepFunctorFiltration (F ⋙ SmoothRep.toRep) n
```

The five universe levels `uG,uH,uV,uC,vC` are independent. In particular the
carrier universe stays `uV`; it is not replaced by a maximum involving either
group universe. There is no topology on any representation carrier and no
assumption of finite dimension, admissibility, finite length, irreducibility,
genericity, a chosen vector, or a saturated universe.

The construction `RepFunctorFiltration.exactSmoothTransport s J` assumes
`[J.PreservesZeroMorphisms]`. Its natural graded comparison additionally assumes
`hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J`. This is exactly the
published generic predicate on injectivity, equality of range and kernel, and
surjectivity of underlying intertwiners. No particular mirabolic or GL derivative
functor is instantiated, and no conclusion of `MinusExactnessStatement` is used.
The image filtration itself needs only zero-map preservation; exactness supplies
the identifications of its grades.

## Canonical smooth lifts

For an actual subfunctor `S` of `F ⋙ SmoothRep.toRep`,
`RepSubfunctor.smoothFunctor S` has value
`SmoothRep.subrepresentation (F.obj X) (S.obj X)`. Its maps are the original
restricted equivariant linear maps. The accepted smoothness-transfer theorem
supplies smoothness through the injective inclusion. `smoothInclusion S` is a
natural transformation into `F`. Forgetting the lift gives `S.toFunctor` by the
identity natural isomorphism `smoothFunctorForgetIso`.

For two actual subfunctors `S,T`, `smoothQuotientFunctor S T` is the actual
smooth quotient of `T(X)` by `S.lowerInUpper T X`, the inverse image of `S(X)`
under the inclusion of `T(X)`. It uses `SmoothRep.quotient` and the actual
quotient maps already used in `RepSubfunctor.quotientFunctor`. Surjective
smoothness transfer supplies its smoothness. The maps are the original descended
quotient maps, so `smoothQuotientForgetIso` is also an identity natural
isomorphism. `smoothQuotientProjection` is the natural smooth quotient map.
These definitions even make sense without containment of `S` in `T`.

For the supplied filtration,
`RepFunctorFiltration.smoothGraded s i` uses the two supplied steps
`i.castSucc` and `i.succ`. Its forgetful comparison
`smoothGradedForgetIso s i` has target exactly `s.graded i`.

## Actual image filtration and endpoints

`RepSubfunctor.exactImage S J` takes the invariant range of the actual
intertwiner `J.map (S.smoothInclusion.app X)` inside `J.obj (F.obj X)`.
Naturality of the smooth inclusion proves that every input-category morphism
preserves this range. This defines actual subfunctor data, not a presumed
filtration or abstract subobject class.

`smoothInclusionOfLE` gives the natural map between two nested smooth
subfunctors. Composing it with the upper inclusion is the lower inclusion.
Applying `J` to this identity proves `exactImage_mono` by taking ranges.
The transported step at every `i : Fin (n+1)` is precisely this image, as
recorded by `exactSmoothTransport_step_obj`.

For the initial step, its inclusion is the zero map because its actual source
submodule is bottom. Zero-map preservation makes the mapped inclusion zero,
so its range is bottom (`exactImage_zero`). Thus no target zero object or target
filtration is assumed. For the final step the original inclusion is bijective
because the supplied source submodule is top. Its equivariant inverse gives a
smooth isomorphism; applying `J` keeps it an isomorphism and hence a surjection.
Its image is top (`exactImage_top`). These arguments establish the required
endpoints from the supplied data.

## Exactness and natural quotient comparison

`ExactSmoothTransport.map_injective` derives preservation of every injective
intertwiner from `hJ`: complete the map to the actual smooth quotient by its
range, and apply the generic short-exactness premise. The range/kernel identity
is the module quotient's kernel formula. Consequently `exactImageHom`, the
natural map from `S.smoothFunctor ⋙ J ⋙ SmoothRep.toRep` onto its image, is
bijective at every object. `exactImageIso` packages these maps as a natural
isomorphism. The inverse is equivariant and natural because it is the inverse
of this natural isomorphism.

When `S ≤ T`, the map from `S` to `T` is injective and its range is exactly the
kernel of `smoothQuotientProjection S T`; the latter is surjective. Applying
`hJ` proves the same three facts after `J`. Define `exactImageQuotientMap` by
the inverse of `exactImageIso T J hJ`, followed by the mapped smooth quotient
projection. It is a natural transformation from the upper image functor to
`S.smoothQuotientFunctor T ⋙ J ⋙ SmoothRep.toRep`.

Its kernel is exactly the actual inverse image of the lower image in the upper
image (`exactImageQuotientMap_kernel`). On a representative `v` in `J(T(X))`,
this follows by factoring the lower ambient inclusion through the upper one,
using injectivity of the mapped upper inclusion, and using
`range (J.map (S → T)) = ker (J.map (T → T/S))`. Its surjectivity follows from
surjectivity of the mapped quotient projection
(`exactImageQuotientMap_surjective`). The published
`RepSubfunctor.quotientNatIsoOfSurjective` therefore yields
`exactImageQuotientIso`. That construction descends natural maps to actual
module quotients, proves equivariance and naturality on representatives, and
forms their inverse isomorphisms from bijectivity.

For successive steps this is
`RepFunctorFiltration.exactSmoothTransportGradedIso s J hJ i`:

```lean
(s.exactSmoothTransport J).graded i ≅
  s.smoothGraded i ⋙ J ⋙ SmoothRep.toRep
```

This is an isomorphism of functors on all of `C`. It is not merely a family of
objectwise comparisons. Its canonical formula
`exactSmoothTransportGradedIso_projection` says that the class of the image of
`v : J(T(X))` is sent to `J.map (T → T/S) v`. Thus the comparison also commutes
with the canonical quotient projections on actual representatives.

## Supplied pieces and gluing

`ExactSmoothTransport.liftNatIso` uses fullness of the smooth inclusion to lift
any natural algebraic isomorphism between underlying smooth functors, retaining
its forward maps, inverse maps, naturality and inverse laws.
`RepFunctorFiltration.exactSmoothTransportPieceIso s J hJ P i e` composes the
canonical graded comparison with `J` applied to the lift of

```lean
e : s.graded i ≅ P ⋙ SmoothRep.toRep
```

to give a natural isomorphism to `P ⋙ J ⋙ SmoothRep.toRep`.
The consequences for a supplied family `P : Fin n → C ⥤ SmoothRep ℂ G` are:

- `RepFunctorFiltration.HasGradedPieces.exactSmoothTransport` transports the
  specified graded identifications on the constructed filtration.
- `HasOrderedFiltration.exactSmoothTransport` transports a witness of the
  ordered filtration relation.
- `IsGluedFrom.exactSmoothTransport` retains the supplied permutation and
  transports its ordered filtration witness.

Every step index and grade index is unchanged. Repeated steps, zero grades,
repeated isomorphic pieces and `n = 0` are included without pruning or an
extra nonzero hypothesis. In the empty case the supplied endpoint equations
force the original functor values to be zero, and the same endpoint proof
applies to their mapped images.

## Internal provenance and proof dependencies

The provenance is elementary invariant-submodule and module-quotient algebra,
combined with functoriality. This is a generic internal prerequisite motivated
by natural filtration arguments; it does not formalize a separate assertion
from BZ77 and cites no original-source theorem as proof evidence.

The mathematical dependencies used by the new declarations are exactly:

1. Actual `RepSubfunctor`, `RepFunctorFiltration`, their natural maps and quotient
   functors, and the definitions of graded pieces, ordered filtration and gluing.
2. `SmoothRep.subrepresentation`, `SmoothRep.quotient` and their canonical
   injective/surjective maps. Their only smoothness proof input is
   `isSmooth_of_injective` / `isSmooth_of_surjective` from
   `Smooth.Transfer.SubquotientProof`, proved by transporting open-subgroup fixed
   vectors along an intertwiner. That proof uses no representation finiteness or
   classification result.
3. The actual natural quotient descent and first isomorphism theorem in
   `Filtration.QuotientFirstIso`, whose proof uses only the quotient definitions,
   the module quotient universal property, and equivariant linear bijections.
4. The definition of the generic predicate `MapsShortExactIntertwiners`, used
   only as the explicit hypothesis `hJ`. Its definition involves the smooth
   categories and underlying linear maps, and refers to no particular minus
   functor. Neither `MinusExactnessStatement` nor a particular exactness theorem
   is a proof input.
5. Mathlib's module ranges, kernels, quotient maps and linear isomorphisms;
   equivariance; categorical functor laws, natural isomorphisms and preservation
   of zero morphisms. No exactness of tensor products or of a particular
   derivative functor is used.

No pre-existing Library pair is edited. Imported results are used by current
Lean names; neither a draft, a Prop-valued target definition, a citation nor a
pending proof task supplies a proved mathematical premise.

## Exact project import closure

At Library base `42ebad9dec7efaf48307e0b6085168e104486dfb`, recursively parsing the
project imports of the new module gives the following 55 imported project
modules, in dependency order. Every imported Lean file and its Markdown pair
matches that base, and every pair exists. The new module itself is the 56th
project module. Direct project imports are `Category.Subquotients`,
`Filtration.QuotientFirstIso` and `Derivative.MirabolicMinusExactnessStatement`;
the other direct import is Mathlib's `CategoryTheory.Limits.Preserves.Shapes.Zero`.

```text
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Category.Basic
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Category.Subquotients
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Group.GL.Basic
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.Mirabolic
Langlands.LocalField.Definitions
Langlands.LocalField.Canonical
Langlands.LocalField.Topology
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.Nonarchimedean
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.Jacquet.Localization
Langlands.HarmonicAnalysis.Basic
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.Dual.Definitions
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Category.Twist
Langlands.Representation.Twist.RealPower
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Normalization.Proof
Langlands.Topology.CompactNormCharacter
Langlands.Group.GL.NormalizedCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
```

The wider import branch comes solely from importing the specified generic
predicate from its published statement module. That branch contains basic
groups, local-field normalization, twists, smoothness, algebraic Whittaker
characters and localization constructions. Its statement definitions are not
used as proved inputs. In particular neither their derivative exactness
conclusions nor their admissibility targets supply any step of this proof.
The actual mathematical dependencies are the five items above.

## Inherited independence audit, condition by condition

All exclusions of the task apply to this module and to every mathematical
prerequisite, including proof successors and downstream consequences. Each row
below is absent both from the complete project import closure and from the
mathematical proof dependencies described above. The closure has no segment,
classification, exhaustion or Whittaker coinvariant-finiteness module. The only
Whittaker imports define algebraic characters, models and their elementary
matrix-coefficient framework; they do not import any finiteness theorem.

| Excluded conclusion or family | Excluded tasks |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` | `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and proof successors |
| `SegmentSocleProductIrreducibility` | `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` |
| `AdjacentUnlinkedSegmentSocleSwap` | `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` |
| `TwoSegmentSocleCommutation` | `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` |
| `LinkedSegmentSocleGluing` | `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` |
| `OrderedMultisegmentSocleExistence` | `23189526-80b0-4828-a6d4-7ebec2cbeef5` |
| `MultisegmentSocleExhaustion` | `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` |
| Analytic segment classification | `aca8805b-054f-4d56-8045-12db7f623404` |
| Special-head multisegment exhaustion | `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` |
| Ordered strong/special-head existence | `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` |
| Quotient coverage | `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` |
| Ordered conversion | `8252833d-c269-41a9-824c-5879e531b23b` |
| Tempered block uniqueness | `52e97845-36bb-457d-b76f-70753334b88c` |
| `GenericSegmentProductUniqueness` | `30341ae4-65f2-4a0e-9283-763db01a409e` |
| `SquareIntegrableLanglandsClassification` | `1cb45da2-7007-4351-a694-594fb148b8d1` |
| Square-integrable exhaustion | `cd8ab97c-0b78-4bce-97c4-d307a28159a4` |
| Regular exhaustion | `bf433f0a-921a-428c-b0c0-6475438125ac` |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment square-integrability | `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` |
| `SegmentHeadProductIrreducibility` | `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` |
| Individual special-head/reverse-socle existence | `67279e36-f3c2-42e3-9302-11729784042e` |
| Individual segment-socle/reverse-head existence | `4ca79bbd-589e-476b-9f65-661e799984b5` |
| `TwoSupercuspidalNonadjacentProductIrreducible` | `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` |
| `TwoSupercuspidalProductStructure`, full-product assembly | `ab61f565-1427-4746-ba77-46097563e962` |
| `SegmentFullJacquetFormula` | `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor |
| `SegmentHeadJacquetFormula` | `55ad1e10-62d8-46b7-a081-909ef0056426` |
| `SegmentSocleJacquetFormula` | `b95105c6-f8bb-4641-ae53-2f49d1e7f034` |
| `SegmentSpecialJacquetExponentNormFormula` | `92aea10f-62ac-4e0b-bd4a-9a80909797c5` |
| `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, all-character single-block finiteness | `62de5903-b616-4b5c-88eb-a066b77c5467` |
| `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` | `5ab445dc-d2b4-4072-80d1-6370870a4a26` |
| `LeviCuspidalCoinvariantFinitenessStatement` | `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` |
| Mirabolic finite-length route using the preceding finiteness | `5428fe2c-013c-482d-aa6e-7df43e7191aa` |

Additional inherited conditions, also checked separately:

- No segment derivative formula, segment-socle/head existence or Jacquet formula,
  or segment classification is a mathematical input. In particular clauses
  (b), (d), (e), (f) of the parent six-statement contribution are unused.
- No Ze80 §3.5 or §9.6 derivative formula, Theorem 4.2 or §9.7 segment product
  irreducibility criterion, or §9.3 analytic/square-integrability result is
  imported or assumed. There is no route through Ze80 §2 to Proposition 1.11.
- No BZ77 derivative result is used without proof. This generic construction
  uses no such result at all: `hJ` is the task's supplied generic functor
  hypothesis, not a replacement for an unconditional derivative Leibniz input.
- There is no tensor-exactness, restriction-sequence, mixed-product, Leibniz,
  character-localization exactness, Jacquet, cuspidal-support, finite-length or
  geometric-lemma proof input. No consumer conclusion establishes an upstream
  premise. The imported localization functor constructions do not assert
  exactness and are not applied by this construction.
- `MinusExactnessStatement` is only an unused definition in the required
  predicate's import module. This task neither proves nor assumes its conclusion.
  Mirabolic minus exactness `b65bc667-6951-4bd5-82af-10fb7046df7f` and GL derivative
  exactness `44f58b77-789a-478c-ba92-9e33b00c8a23` remain separately owned.
- Worker 127's operator pause is preserved; this task did not contact or wake
  Worker 127. Worker 288's all-character/degenerate-character finiteness adapters
  are coordination pointers, not hypotheses or evidence.

The inherited restrictions originate in
`2e5183b1-01e9-44fb-b26c-f4521a25c7c7` revision 2 and the shared upstream
arrangement `3238f371-e9a2-42ce-8b5d-9c4d3400ff55` revision 2. Naming these
owners does not add either task's mathematical conclusion as an input.

## Validation boundary

Development compilation uses environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The complete implementation compiles
without errors or warnings. Inspection of the natural graded comparison reports
exactly the five independent universe levels above and only `propext`,
`Classical.choice` and `Quot.sound`. Compilation is development evidence;
independent semantic review and Library publication are required before this
construction is an accepted prerequisite.
