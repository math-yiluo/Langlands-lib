# Proof of effective finite Banach affinoid algebra descent

This module proves

```
theorem Langlands.Analytic.PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent :
    FiniteAffinoidAlgebraDescentStatement.{u}
```

So effective descent holds for finite Banach affinoid algebras along every
finite full-domain cover. The coefficient field `K` is any complete ultrametric
normed field, including trivially valued fields. The base `R` is any presented
affinoid algebra with arbitrary positive polyradius, and the cover is any
finite full-domain cover of `Domain.whole K R`, including empty covers. The
proof adds no hypothesis to the statement. It uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The proof in this module

The module combines the published intermediate statements
`FiniteAffinoidAlgebraGlobalGenerationStatement` (St1) and
`FiniteAffinoidAlgebraGlobalGenerationReductionStatement` (St2). It proves
them through four short theorems.

1. `FiniteAffinoidAlgebraDescent.pieceMatchingLocalGeneration` proves
   `PieceMatchingLocalGenerationStatement`. Suppose a tuple of matching
   families over a full domain `V` generates every restricted piece on the
   members of a finite cover of `V`. Then it generates the matching algebra
   over `V.algebra`. The theorem applies
   `PieceRefinement.generates_of_piecesGenerate` from `PieceRefinementSections`.
2. `finiteAffinoidAlgebraGlobalGenerationReduction` proves St2. Given a
   generating tuple of matching elements, it returns the `EffectiveRealization`
   built by `FiniteAffinoidAlgebraDescent.effectiveRealizationOfGenerators`
   from `GeneratedEffectiveRealization`.
3. `finiteAffinoidAlgebraGlobalGeneration` proves St1. It applies
   `FiniteAffinoidAlgebraDescent.globalGeneration_of_prerequisites` from
   `PieceInduction` to proofs of its five hypotheses:
   - `pieceMatchingLocalGeneration` (step 1) for
     `PieceMatchingLocalGenerationStatement`;
   - `FiniteAffinoidAlgebraDescent.pieceMatchingGluing` for
     `PieceMatchingGluingStatement`;
   - `finiteCoverBinaryLaurentInduction` for
     `FiniteCoverBinaryLaurentInductionStatement`;
   - `domainBinaryLaurentSplitSquare` for
     `DomainBinaryLaurentSplitSquareStatement`;
   - `BoundedAlgHom.splitSquareModuleGeneration` for
     `BoundedAlgHom.SplitSquareModuleGenerationStatement`.
4. `finiteAffinoidAlgebraDescent` proves the target. For the given data it
   takes `n` and a generating tuple `s` from St1, then applies St2 to them.

## Mathematical route

The argument follows the structure of Kiehl's theorem. First, finitely many
global matching elements are found whose projections generate every local
algebra over its cover algebra (St1). Then these generators give a bounded
finite presentation of the matching algebra, and the presentation gives the
effective realization (St2).

St1 is proved by induction along binary Laurent splits, with a Cartan-type
lemma at each split. Matching families over a full domain `V` are the elements
of `pieceMatching V`. The induction carries the weaker property
`PiecesGenerate`: generation of each restricted piece over the algebra of
`V ∩ cᵢ`. Unlike generation of `pieceMatching V` itself, this property
restricts to smaller domains without a flatness argument. Inside each
induction step, step 1 turns piece generation into generation of the matching
families, so that the Cartan-type lemma applies to them as modules.

- `PieceGeneration`, `PieceBaseCase`: base case. On a domain inside one cover
  member, generators of that member's local algebra give matching families
  that generate all pieces.
- `PieceMatchingGluingProof`: matching families glue uniquely along finite
  covers (Tate acyclicity, from the Library's `DomainAlgebraGluing`).
- `LaurentInductionProof`: for a cover with at least one member, a property
  of full domains holds for the whole domain if it holds on domains inside
  cover members and passes through binary Laurent splits `{|a| ≤ ρ}`,
  `{|a| ≥ ρ}`. Here `a` is any element of the domain algebra and `ρ` is any
  positive real radius. `PieceInduction` treats the empty cover separately:
  there the empty family works.
- `BinaryLaurentSplitProof`: every such binary Laurent split of a full domain
  is a split square of bounded algebra maps. No strict-radius or
  nontrivial-valuation assumption is needed.
- `SplitSquareGenerationProof`: the Cartan-type lemma. Over a split square
  `A → A₁, A₂ → A₁₂`, let `M₁` and `M₂` be finitely generated modules whose
  images both span a module `M₁₂`. Then there are finite families in `M₁` and
  `M₂` with equal images in `M₁₂` that generate `M₁` and `M₂`. The proof
  solves linear systems by successive approximation, using the bounded
  splitting of the square.
- `PieceInduction`: combines these into
  `globalGeneration_of_prerequisites`.

St2 is proved by the following modules of the Library:

- `LocalBaseChangeEquivalence`: further base changes of local pieces and their
  pair transitions.
- `PieceRefinementData`, `PieceRefinementSections`: local algebras on the
  intersection refinement of two covers. They also prove
  `PieceRefinement.generates_of_piecesGenerate` (used in step 1).
- `MatchingCoefficientLifts`: norm-controlled global coefficients for a locally
  generating matching tuple. This uses the free square-zero extension and
  bounded residue gluing, and gives `IsFiniteBanach` for the matching
  structural map.
- `GeneratedEffectiveRealization`: the full `EffectiveRealization`, assembled
  from the generator quotient, the local comparison equivalences, and the
  Library's `RealizationAssembly`.

Each module's Markdown describes its proof in detail.

## Modules

All modules are in
`Langlands/Geometry/Analytic/GeneralizedAffinoid/FiniteAffinoidAlgebraDescent/`.
The proof consists of the following modules:

| Module | Role |
| --- | --- |
| `PieceGeneration` | explicit pushout generators |
| `PieceBaseCase` | cocycle, base case |
| `PieceInduction` | St1 from its five hypotheses |
| `PieceMatchingGluingProof` | `PieceMatchingGluingStatement` |
| `LaurentInductionProof` | `FiniteCoverBinaryLaurentInductionStatement` |
| `BinaryLaurentSplitProof` | `DomainBinaryLaurentSplitSquareStatement` |
| `SplitSquareGenerationProof` | `SplitSquareModuleGenerationStatement` |
| `Proof` | this assembly |

It imports the following modules of the Library:
`LocalBaseChangeEquivalence` (further base change),
`PieceRefinementData` (intersection refinement), `PieceRefinementSections`
(refined sections, step 1), `MatchingCoefficientLifts` (uniform coefficient
lifts) and `GeneratedEffectiveRealization` (St2 construction).

The statements St1, St2, `PieceMatchingLocalGenerationStatement`,
`PieceMatchingGluingStatement`, `FiniteCoverBinaryLaurentInductionStatement`,
`DomainBinaryLaurentSplitSquareStatement` and
`SplitSquareModuleGenerationStatement` are published in the Library.

## Provenance

The proof route is an internal derivation and differs in its details from the
literature. Kiehl's theorem on effective finite-module descent and its
extension to general affinoids and trivial valuations are in Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's Theorem
and Remark 1.2.1(ii), printed p.15 / PDF p.12. The application to finite
algebras, Lemma 1.2.12, is on printed p.20 / PDF p.17 (registered source
`berkovich-1993-etale-cohomology`). The Banach conventions follow Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
§§2.1.9–2.1.12. The reduction to binary Laurent splits follows Piotr Achinger,
*Introduction to non-Archimedean Geometry* (lecture notes, November 22, 2020),
§7.1–§7.3, pp.64–67 (registered source
`achinger-2020-non-archimedean-geometry-nov22`). Our version works with
arbitrary real radii and does not use scalar extension to a nontrivially
valued field.
