# Uniform dynamic compression from the remaining representation inputs

Author: Worker 4899. Module
`Langlands.Representation.Exponents.UniformCompressionRepresentationReduction`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This is an internal reduction for proof task
`47e556e6-6b2a-40dc-ba66-d6a0585f5220`, whose target is the unchanged Library
proposition `UniformCompressionStabilizationStatement.{u,v}` (Renard 2026,
VI.9.1 Proposition, printed p.197 / PDF p.203). It does not prove that
target. It shortens the list of premises of the published conditional assembly
`uniformCompressionStabilization_of_nativeStatements` (module
`UniformCompressionNativeAssembly`) from thirteen to five. Each discharged premise
is supplied by a published theorem. The five that remain are the
representation-theoretic statements.

## Declarations

1. `arbitraryParabolicQuotientCompact_of_dynamicTheorems :
   RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u}`.
   Its type is exactly the published compactness proposition: for every
   represented parabolic `p` of a connected reductive group over a
   nonarchimedean local field, with the statement's own topology and instances,
   `CompactSpace (Induction.LeftQuotient (pointImage p))`.
2. `rationalSupercuspidalJacquetFamilyFinite_of_structuralTheorems :
   RationalSupercuspidalJacquetFamilyFiniteStatement.{u,uV}`, for arbitrary
   independent universes `u` and `uV`. Its type is exactly the published VI.9.2
   input (Renard printed pp.198–199 / PDF pp.204–205). For the actual universal
   induced family of an irreducible admissible supercuspidal representation,
   every compact-open fixed module of every output normalized Jacquet action is
   finite over the full rational-norm regular algebra.
3. `UniformCompressionRepresentationReductionStatement : Prop`, the implication

   `RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
   RationalCuspidalInertiaProductDecompositionStatement.{u, max u v} →
   RationalCuspidalInertiaFinitenessStatement.{u, max u v} →
   RationalUniversalSmallProgeneratorStatement.{u, max u v} →
   RationalCuspidalInducedEmbeddingStatement.{u, max u v} →
   UniformCompressionStabilizationStatement.{u, v}`.

   Every premise is an existing Library proposition, used unchanged. None of
   them is a compression or stabilization statement.
4. `uniformCompressionStabilization_of_representationStatements`, the same
   implication with the five premises as named hypotheses, and
   `uniformCompressionRepresentationReduction`, which proves item 3 at
   arbitrary independent universes `u` and `v`.

## Implemented proofs

**Item 1.** After introducing the field, the group and the represented
parabolic, the proof applies the published helper
`RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic` to the
published theorems `GroupScheme.parabolicDynamic` (every parabolic is a dynamic
parabolic `P(χ)`) and `BruhatTits.dynamicParabolicQuotientCompact`
(compactness of both coset quotients of the rational points of every dynamic
parabolic). The helper rewrites the literal point image of `p` as the rational
points of `P(χ)` and uses the left-coset half of the compactness conclusion.
The helper installs the same `pointTopology` as the statement. The standalone
proof of this proposition is the separate task
`c1ce4629-6768-4eb5-b4ee-0086526913ea`. Item 1 is recorded here because item 2
needs it.

**Item 2.** The published conditional theorem
`Plancherel.rationalSupercuspidalJacquetFamilyFinite_of_structural` derives the
statement from two structural propositions:
`RepresentedParabolicDoubleCosetStatement` and
`ArbitraryParabolicQuotientCompactStatement`. The first is supplied by the
published assembly
`GroupScheme.representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs`,
applied to six published theorems: `rationalBruhat`,
`genericMinimalParabolic`, `minimalParabolicConjugacy`,
`parabolicIntersectionCentralizer`, `parabolicDynamic` and
`smoothMaximalSplitTorusConjugacy`. The second is item 1. The resulting
theorem has no hypotheses. Inspecting it in the Lean service reports only the
axioms `propext`, `Classical.choice` and `Quot.sound`. The proof task for this
proposition is `c1f3c743-2a62-415c-8640-714b9f6a27c4`. Item 2 is recorded here
because the uniform target needs it.

**Item 4.** The theorem applies `uniformCompressionStabilization_of_nativeStatements`
and fills eight of its thirteen premises:

| Premise of the native assembly | Supplied by |
| --- | --- |
| `GenericMinimalParabolicStatement.{u}` | `GroupScheme.genericMinimalParabolic` |
| `ParabolicDynamicStatement.{u}` | `GroupScheme.parabolicDynamic` |
| `SmoothMaximalSplitTorusConjugacyStatement.{u}` | `GroupScheme.smoothMaximalSplitTorusConjugacy` |
| `StandardCocharacterStatement.{u}` | `GroupScheme.standardCocharacter` |
| `StandardLeviIntersectionStatement.{u}` | `GroupScheme.standardLeviIntersection` |
| `RelativeRootSystemStatement.{u}` | `GroupScheme.relativeRootSystem` |
| `BruhatTits.DynamicParabolicQuotientCompactStatement.{u}` | `BruhatTits.dynamicParabolicQuotientCompact` |
| `RationalSupercuspidalJacquetFamilyFiniteStatement.{u, max u v}` | item 2 at `uV := max u v` |

The other five premises, `RationalPointsIrreducibleAdmissibleStatement`,
`RationalCuspidalInertiaProductDecompositionStatement`,
`RationalCuspidalInertiaFinitenessStatement`,
`RationalUniversalSmallProgeneratorStatement` and
`RationalCuspidalInducedEmbeddingStatement`, are passed on unchanged at
`{u, max u v}`, the universes at which the native assembly uses them. The
conclusion is the unchanged `UniformCompressionStabilizationStatement.{u, v}`.
It keeps the exponent chosen before the carrier and the representation, both
stationary power-chain equalities, complementarity, and every dynamic-parabolic
and central-contraction hypothesis. The Markdown of
`UniformCompressionNativeAssembly` explains how the native assembly uses these
hypotheses. In summary, it reduces to eventual stability on each smooth object
by the countable-sum diagonal argument, embeds objects into finite sums of
cuspidal inductions, and proves stability for those inductions from coefficient
finiteness and the localization criterion. That criterion uses the Iwahori
contraction and the centrality of `g` in the dynamic Levi.

## Remaining obligations

To prove the target with this reduction, the five remaining premises must be
proved. Their proof tasks are:

- `RationalPointsIrreducibleAdmissibleStatement` (Jacquet's theorem):
  `173e44ba-079b-4597-a13b-1aab371a4ec9`;
- `RationalCuspidalInertiaProductDecompositionStatement` (VI.3.5):
  `b1a82b53-e942-41b3-9f25-dec52736e712`;
- `RationalCuspidalInertiaFinitenessStatement` (VI.3.4 concluding remark):
  `61b5cb94-c808-4499-9efb-ec1ae6c0cecb`;
- `RationalUniversalSmallProgeneratorStatement` (VI.4.1):
  `0ba788d6-b9d9-4a76-a017-972f8cad288f`;
- `RationalCuspidalInducedEmbeddingStatement` (VI.7.2):
  `198824c2-4e2f-40c1-94a0-07fa748bede9`.

## Provenance and scope

This is an internal composition of published Library theorems. It makes no new
literature claim. The source context is David Renard, *Représentations des
groupes réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: VI.9.1
Proposition (printed p.197 / PDF p.203) and its proof in VI.9.2–VI.9.3
(printed pp.198–200 / PDF pp.204–206). The universes of the target are
independent, and the reduction adds no admissibility, finite-length,
finite-generation or dimension premise on the representations in the target.
