# Exact functors on actual natural smooth filtrations

Internal construction.

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
restricted equivariant linear maps. The published smoothness-transfer theorem
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

The mathematical dependencies used by this module's declarations are exactly:

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

Imported results are used by their Lean names; neither a Prop-valued target
definition nor a citation supplies a proved mathematical premise.

## Exact project import closure

At Library base `42ebad9dec7efaf48307e0b6085168e104486dfb`, recursively parsing the
project imports of this module gives the following 55 imported project
modules, in dependency order. Every imported Lean file and its Markdown pair
matches that base, and every pair exists. This module itself is the 56th
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

## Independence conditions, one by one

The exclusions below apply to this module and to every mathematical
prerequisite, including downstream consequences. Each row
below is absent both from the complete project import closure and from the
mathematical proof dependencies described above. The closure has no segment,
classification, exhaustion or Whittaker coinvariant-finiteness module. The only
Whittaker imports define algebraic characters, models and their elementary
matrix-coefficient framework; they do not import any finiteness theorem.

| Excluded conclusion or family |
| --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` |
| `SegmentSocleProductIrreducibility` |
| `AdjacentUnlinkedSegmentSocleSwap` |
| `TwoSegmentSocleCommutation` |
| `LinkedSegmentSocleGluing` |
| `OrderedMultisegmentSocleExistence` |
| `MultisegmentSocleExhaustion` |
| Analytic segment classification |
| Special-head multisegment exhaustion |
| Ordered strong/special-head existence |
| Quotient coverage |
| Ordered conversion |
| Tempered block uniqueness |
| `GenericSegmentProductUniqueness` |
| `SquareIntegrableLanglandsClassification` |
| Square-integrable exhaustion |
| Regular exhaustion |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment square-integrability |
| `SegmentHeadProductIrreducibility` |
| Individual special-head/reverse-socle existence |
| Individual segment-socle/reverse-head existence |
| `TwoSupercuspidalNonadjacentProductIrreducible` |
| `TwoSupercuspidalProductStructure`, full-product assembly |
| `SegmentFullJacquetFormula` |
| `SegmentHeadJacquetFormula` |
| `SegmentSocleJacquetFormula` |
| `SegmentSpecialJacquetExponentNormFormula` |
| `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, all-character single-block finiteness |
| `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` |
| `LeviCuspidalCoinvariantFinitenessStatement` |
| Mirabolic finite-length route using the preceding finiteness |

Further conditions, also checked separately:

- No segment derivative formula, segment-socle/head existence or Jacquet formula,
  or segment classification is a mathematical input.
- No Ze80 §3.5 or §9.6 derivative formula, Theorem 4.2 or §9.7 segment product
  irreducibility criterion, or §9.3 analytic/square-integrability result is
  imported or assumed. There is no route through Ze80 §2 to Proposition 1.11.
- No BZ77 derivative result is used without proof. This generic construction
  uses no such result at all: `hJ` is the supplied generic functor
  hypothesis, not a replacement for an unconditional derivative Leibniz input.
- There is no tensor-exactness, restriction-sequence, mixed-product, Leibniz,
  character-localization exactness, Jacquet, cuspidal-support, finite-length or
  geometric-lemma proof input. No consumer conclusion establishes an upstream
  premise. The imported localization functor constructions do not assert
  exactness and are not applied by this construction.
- `MinusExactnessStatement` is only an unused definition in the required
  predicate's import module. This module neither proves nor assumes its
  conclusion, and uses neither mirabolic minus exactness nor GL derivative
  exactness.
- The all-character and degenerate-character finiteness adapters are neither
  hypotheses of this module nor evidence for it.

## Compilation

With Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, the complete implementation compiles
without errors or warnings. Inspection of the natural graded comparison reports
exactly the five independent universe levels above and only `propext`,
`Classical.choice` and `Quot.sound`.
