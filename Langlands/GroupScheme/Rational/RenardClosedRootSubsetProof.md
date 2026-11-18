# Assembly of the Renard V.4.2 component proofs

Module `Langlands.GroupScheme.Rational.RenardClosedRootSubsetProof`. Namespace
`Langlands.GroupScheme`. Universe parameter `u`.

The theorem `renardClosedRootSubsets` has exactly the type
`RenardClosedRootSubsetStatements.{u}`, the published proposition in
[RenardClosedRootSubsetStatements](RenardClosedRootSubsetStatements.md).
This module supplies a logical assembly of published proofs. Its provenance is
the Library target and the eight component theorems below; the target's paired
Markdown records the comparison with Renard, *Représentations des groupes
réductifs p-adiques*, edition dated 9 July 2026, §V.4.2.

## Implemented proof

The definition of `RenardClosedRootSubsetStatements` is an eight-part,
right-associated conjunction. The proof is the anonymous constructor pairing
these existing theorems, in the order of that definition, all at universe `u`.
Each proof module is imported directly by its Lean name.

| Component statement | Published theorem | Imported proof module |
| --- | --- | --- |
| `ConvexRootSubsetHullStatement` | `convexRootSubsetHull` | [ConvexRootSubsetHullProof](ConvexRootSubsetHullProof.md) |
| `UnipotentRootSubsetCocharacterStatement` | `unipotentRootSubsetCocharacter` | [UnipotentRootSubsetCocharacterProof](UnipotentRootSubsetCocharacterProof.md) |
| `SymmetricRootSubsetWeylStatement` | `symmetricRootSubsetWeyl` | [SymmetricRootSubsetWeylProof](SymmetricRootSubsetWeylProof.md) |
| `StandardParabolicRootTripleStatement` | `standardParabolicRootTriple` | [StandardParabolicRootTripleProof](StandardParabolicRootTripleProof.md) |
| `RootSubsetGroupExistenceStatement` | `rootSubsetGroupExistence` | [RootSubsetGroupExistenceProof](RootSubsetGroupExistenceProof.md) |
| `StandardParabolicRootSubsetGroupStatement` | `standardParabolicRootSubsetGroup` | [StandardParabolicRootSubsetGroupProof](StandardParabolicRootSubsetGroupProof.md) |
| `ConvexRootSubsetGroupIntersectionStatement` | `convexRootSubsetGroupIntersection` | [ConvexRootSubsetGroupIntersectionProof](ConvexRootSubsetGroupIntersectionProof.md) |
| `UnipotentRootSubsetGroupIntersectionStatement` | `unipotentRootSubsetGroupIntersection` | [UnipotentRootSubsetGroupIntersectionProof](UnipotentRootSubsetGroupIntersectionProof.md) |

All theorem and statement names in the table are in `Langlands.GroupScheme`.
The mathematical proofs of the components remain in the linked modules; the
only proof step implemented here is conjunction introduction.

## Inherited scope

The target quantifies over an arbitrary field of universe `u`, a connected
reductive group and a maximal split torus. The components that use a minimal
parabolic retain their generic-cocharacter hypotheses.

The combinatorial statements use the two ambient root sets allowed by
`IsRelativeRootAmbient`: the possibly nonreduced `relativeRoots i` and Renard's
reduced `RelativeRoot.indivisibleRoots i`. The convex group-intersection
component uses the reduced ambient set and requires both subsets to be convex;
the unipotent group-intersection component uses the possibly nonreduced
relative roots.

The groups denoted by `G(X)` and `U(X)` satisfy the published closed-subgroup
minimality predicates `IsRootSubsetGroup` and `IsRootSubsetUnipotentGroup`.
The intersection conclusions are exactly `HasReducedPointIntersection`,
quantifying over reduced test schemes.

The target excludes `ClosedRootSubsetGroupIntersectionStatement`, the
Borel–Tits 3.22(b) assertion discussed in the target's Markdown and the
[published erratum note](../../../notes/errata/borel-tits-1965-closed-root-intersection.md).
