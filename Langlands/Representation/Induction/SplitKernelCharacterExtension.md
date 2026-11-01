# Invariant split-kernel character extension

Worker 200 constructs the clause-1 elementary character extension for task
`867199fa-9617-424f-8b81-cbf685f3759e` revision 2, using the interface agreed
with Worker 118. The namespace is `Langlands.Induction.SplitKernelLocalization`.

## Actual constructions and defining laws

The groups `G : Type uG` and `L : Type uL` have independent universes.
They need not be commutative, finite, locally compact, or nontrivial. Let
`r : G →* L`, `s : L →* G`, and `hrs : ∀ l, r (s l) = l`. Write `N = r.ker`.

`kernelConjugate r s l n` is the actual element of `N` whose ambient value
is `(s l)⁻¹ * n * s l`. Its kernel membership follows by applying `r` and
using `r n = 1`; this construction does not need the retraction identity.
`SectionInvariant r s theta` is a proposition, exactly
`∀ l n, theta (kernelConjugate r s l n) = theta n`.
It is the structural character-invariance hypothesis, not a comparison theorem.

`kernelCoordinate r s hrs g` is the actual element of `N` with value
`g * (s (r g))⁻¹`. The proof of membership applies `r` and then `hrs`.
`kernelCoordinate_mul` proves the precise cocycle formula

```text
k(g*h) = k(g) * kernelConjugate r s (r g)⁻¹ (k(h)).
```

The conjugation index is `(r g)⁻¹`. Consequently the ambient conjugating
element on the left of `k(h)` is `s (r g)`, as required by the decomposition
`g = k(g) * s (r g)`. The implemented proof is subtype extensionality,
homomorphism multiplication/inversion, associativity, and inverse cancellation.
The three subsequent coordinate lemmas give `k(1)=1`, `k(n)=n` for `n : N`,
and `k(s(l))=1`.

Given `theta : N →* ℂˣ` and `hTheta : SectionInvariant r s theta`,
`characterExtension r s hrs theta hTheta : G →* ℂˣ` has exactly the formula

```text
characterExtension r s hrs theta hTheta g
  = theta ⟨g * (s (r g))⁻¹, kernel membership proof⟩.
```

The homomorphism multiplication field applies the cocycle formula, then
`theta.map_mul`, then `hTheta (r g)⁻¹`. Its unit field uses `k(1)=1`.
`characterExtension_apply` exposes the defining formula through the actual
`kernelCoordinate`; `characterExtension_kernel` and
`characterExtension_section` prove the requested restrictions to `theta`
and to the trivial character. `characterExtension_mul` exposes the actual
homomorphism multiplication law. The character on any subgroup intersection
may remain nontrivial.

`characterExtension_ker` identifies the underlying set of the extension
kernel with the inverse image of `theta.ker` under `kernelCoordinate`.
This is an equality of sets proved by extensionality and reflexivity;
`kernelCoordinate` itself is not claimed to be a homomorphism.

For topology, assume a topological group structure on `G`, a topology on `L`,
and `hr : Continuous r`, `hs : Continuous s`.
`continuous_kernelCoordinate` is continuity of the displayed multiplication
and inverse, followed by passage to the kernel subtype. A topological group
structure on `L` is permitted but unnecessary for this proof.
For an actual `theta : Langlands.Induction.SmoothCharacter ℂ N`,
`smoothCharacterExtension r s hrs hr hs theta hTheta` is an actual
`Langlands.Induction.SmoothCharacter ℂ G`. Its homomorphism is the preceding
extension of `theta.toMonoidHom`; its kernel is open because it is the
preimage of `theta.isOpen_ker` under `continuous_kernelCoordinate`.
`smoothCharacterExtension_toMonoidHom` gives the exact underlying
homomorphism equality. The construction assumes no continuity of `theta`
into an analytic topology on `ℂˣ`, and no topology on a coefficient module.

No representation carriers occur in this module, so it imposes no relationship
between the independent carrier universes in subsequent quotient constructions.
It excludes no zero module or intertwiner. Clauses 2 and 3, the localized
section actions and their natural quotient transports, belong to the separate
entry construction; they are not claimed here.

## Provenance and normalization

This is internal elementary group algebra. Bernstein–Zelevinsky (1977),
source `bernstein-zelevinsky-1977-induced-i`, §1.8 printed pp.444–445
(PDF pp.5–6) and §7.2 printed p.471 (PDF p.32), motivates character
localization and the later orbit application but is not used as a proof
premise. The source text and page images were read directly. Its retained
content SHA256 is
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
No source-specific errata file was found in the project or Library notes.

Section 1.8 defines localization by the span of `rho(u)v-theta(u)v` and
includes a modulus factor in its localized action. The present character
extension is internal group algebra and has no modulus, Haar measure,
determinant, induction, or normalization factor. Section 7.2 describes the
orbits used for mixed minus functors; none of its comparison conclusions
is assumed or proved here.

## Complete project import closure

The only direct project import is
`Langlands.Representation.Induction.Definitions`. The entire transitive
project closure, with every source inspected, is exactly:

1. `Langlands.Representation.Induction.Definitions`.
2. `Langlands.Representation.Category.Basic`.
3. `Langlands.Representation.Smooth.Definitions`.
4. `Langlands.Representation.Smooth.SmoothPart.Definitions`.
5. `Langlands.Representation.Twist.Definitions`.

The direct Mathlib import is `Mathlib.Basic.Complex.Basic`.
The project edges are: induction definitions import category basic, smooth-part
definitions, and twist definitions; category basic and smooth-part definitions
import smooth definitions; smooth definitions and twist definitions have no
project imports. Thus this list is transitively closed. The existing
`SmoothCharacter` structure comes from induction definitions. None of the
other project constructions is applied by the new proofs. In particular,
although that foundational file also defines actual induction and compact
induction, this module does not apply their constructors or conclusions.
The full source audit found only foundational categories, scalar twists,
open fixing subgroups, and directly constructed covariant-function spaces.
There is no derivative, geometric lemma, segment, classification, finiteness,
or compact-induction comparison proof in this closure.

The larger modules `Induction.CharacterTwistProof`,
`Induction.SplitKernelCovariance`, `Induction.SplitStagesRetraction`,
`Induction.SplitKernelCharacter`, `Induction.SplitStagesComparison`, and
all `Jacquet` modules are not imports or proof dependencies of this pair.
The extension requires none of their integration or quotient results.

## Condition-by-condition proof-dependency audit

| Clause-1 obligation | Actual direct proof inputs | Transitive mathematical dependency |
| --- | --- | --- |
| Actual inverse conjugate and coordinate in `r.ker` | Group homomorphism laws, `n.property`, and `hrs` for the coordinate | Mathlib subgroup and group laws |
| Coordinate product formula | Subtype extensionality, multiplication/inversion preservation, cancellation | Mathlib group laws |
| Actual extension homomorphism and multiplication law | Coordinate product formula, `theta.map_mul`, `hTheta (r g)⁻¹` | The two preceding rows only |
| Kernel and section restrictions | The proved coordinate restrictions and `theta.map_one` | Group identities and `hrs` |
| Kernel set formula | The extension's defining formula | Reflexivity and set extensionality |
| Continuous coordinate | Continuity of multiplication and inverse in `G`, `hr`, `hs` | Mathlib continuity and induced subtype topology |
| Actual smooth extension and its open kernel | Existing `SmoothCharacter` structure, `theta.isOpen_ker`, continuous coordinate | The preceding row and preimages of open sets |

Every row is independent, directly and transitively, of the full inherited
exclusion union. This is a proof audit as well as an import audit: the only
project type used in a proof field is the existing smooth-character structure;
no consumer conclusion, conditional assembly, pending proof, proposition
definition, or citation is used as a proved input. The following exhaustive
grouping records the entire union, including successors and downstream
consequences of every item. Each group is absent from every row above.

- All-character and Whittaker finiteness:
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
  `62de5903-b616-4b5c-88eb-a066b77c5467`;
  `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`,
  `5ab445dc-d2b4-4072-80d1-6370870a4a26`;
  `LeviCuspidalCoinvariantFinitenessStatement`,
  `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`; and the dependent mirabolic
  finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa`.
- Generic, head, and analytic classification:
  `GenericSegmentProductUniqueness`,
  `30341ae4-65f2-4a0e-9283-763db01a409e`;
  `SegmentHeadProductIrreducibility`,
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`;
  analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`;
  `SegmentSpecialEssentialSquareIntegrability`,
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`;
  `SquareIntegrableLanglandsClassification`,
  `1cb45da2-7007-4351-a694-594fb148b8d1`; and tempered uniqueness
  `52e97845-36bb-457d-b76f-70753334b88c`.
- Existence, exhaustion, and coverage:
  individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`;
  individual segment-socle/reverse-head existence
  `4ca79bbd-589e-476b-9f65-661e799984b5`;
  multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
  ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
  quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
  ordered conversion `8252833d-c269-41a9-824c-5879e531b23b`;
  square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
  regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`;
  `OrderedMultisegmentSocleExistence`,
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`; and
  `MultisegmentSocleExhaustion`,
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.
- Segment-socle products, commutation, and gluing:
  `UnlinkedSegmentSocleProductIrreducible`,
  `23e98d90-6055-4e35-91a9-b0f5d8a84961`;
  `LinkedSegmentSocleReverseProductStructure`,
  `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`;
  `LinkedSegmentSoclePairReducible`,
  `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`;
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `7ff2a1e9-89dc-439e-a861-a567b3db92bf`;
  `SegmentSocleProductIrreducibility`,
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`;
  `AdjacentUnlinkedSegmentSocleSwap`,
  `e3634665-571b-4852-9f4c-bab8a1053434`,
  `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`;
  `TwoSegmentSocleCommutation`,
  `426911b4-6620-413f-8065-04b25287f3bd`,
  `66e3b87c-647e-41e4-af18-df4d436765f0`;
  `LinkedSegmentSocleGluing`,
  `c84cd52c-3ff3-4024-be50-8b84dd480888`,
  `6780b79c-9526-46aa-b8b4-00377d68b1ea`.
- Two-supercuspidal products:
  `TwoSupercuspidalNonadjacentProductIrreducible`,
  `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`;
  `TwoSupercuspidalProductStructure`,
  `ab61f565-1427-4746-ba77-46097563e962`.
- All segment derivative, segment-socle/head existence, and Jacquet formulas:
  `SegmentFullJacquetFormula`,
  `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor;
  `SegmentHeadJacquetFormula`,
  `55ad1e10-62d8-46b7-a081-909ef0056426`;
  `SegmentSocleJacquetFormula`,
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`;
  `SegmentSpecialJacquetExponentNormFormula`,
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`; and clauses (b), (d), (e), (f)
  of the six-statement parent of derivative task
  `2e5183b1-01e9-44fb-b26c-f4521a25c7c7`.
- The additional source and general-input restrictions: no Ze80 §3.5 or §9.6
  segment derivative formula, §4.2 or §9.7 product irreducibility criterion,
  §9.3 analytic or square-integrability result, classification or exhaustion
  theorem is used. No BZ77 derivative theorem, general derivative functor
  result, exactness, Leibniz filtration, geometric lemma, cuspidal support,
  finite-length, tensor, or top-localization theorem is used. In particular,
  no unproved general derivative input or consumer-supplied replacement
  assumption enters the construction. The group name `plusSubgroup` does
  not occur, and no plus-functor result is used.

These restrictions continue to bind the eventual action entry and later
comparisons; this lower pair does not weaken them or arrange successors.
Worker 127's operator pause and all current operator suspensions are preserved.

## Validation boundary

The module compiles in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0 and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
The development check has zero errors and warnings. Compilation and the
intrinsic construction proofs do not themselves establish independent
semantic acceptance or Library publication.
