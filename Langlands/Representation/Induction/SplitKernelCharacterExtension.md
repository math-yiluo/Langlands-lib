# Invariant split-kernel character extension

This module constructs the elementary character extension (clause 1) of the
split-kernel localization assembled in `SplitKernelLocalizationData`, which
imports it together with `SplitKernelSectionAction`. The namespace is
`Langlands.Induction.SplitKernelLocalization`.

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
`characterExtension_section` prove the restrictions to `theta`
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
entry construction `SplitKernelLocalizationData`; they are not claimed here.

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

Every row is independent, directly and transitively, of the full
exclusion union below. This is a proof audit as well as an import audit: the only
project type used in a proof field is the existing smooth-character structure;
no consumer conclusion, conditional assembly, unproved proposition, proposition
definition, or citation is used as a proved input. The following exhaustive
grouping records the entire union, including the modules that prove each
item and its downstream consequences. Each group is absent from every row above.

- All-character and Whittaker finiteness:
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`;
  `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`;
  `LeviCuspidalCoinvariantFinitenessStatement`; and the dependent mirabolic
  finite-length route.
- Generic, head, and analytic classification:
  `GenericSegmentProductUniqueness`;
  `SegmentHeadProductIrreducibility`;
  analytic segment classification;
  `SegmentSpecialEssentialSquareIntegrability`;
  `SquareIntegrableLanglandsClassification`; and tempered uniqueness.
- Existence, exhaustion, and coverage:
  individual special-head/reverse-socle existence;
  individual segment-socle/reverse-head existence;
  multisegment exhaustion;
  ordered strong-head existence;
  quotient coverage;
  ordered conversion;
  square-integrable exhaustion;
  regular exhaustion;
  `OrderedMultisegmentSocleExistence`; and
  `MultisegmentSocleExhaustion`.
- Segment-socle products, commutation, and gluing:
  `UnlinkedSegmentSocleProductIrreducible`;
  `LinkedSegmentSocleReverseProductStructure`;
  `LinkedSegmentSoclePairReducible`;
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`;
  `SegmentSocleProductIrreducibility`;
  `AdjacentUnlinkedSegmentSocleSwap`;
  `TwoSegmentSocleCommutation`;
  `LinkedSegmentSocleGluing`.
- Two-supercuspidal products:
  `TwoSupercuspidalNonadjacentProductIrreducible`;
  `TwoSupercuspidalProductStructure`.
- All segment derivative, segment-socle/head existence, and Jacquet formulas:
  `SegmentFullJacquetFormula` and its proof `segmentFullJacquetFormula`
  (module `Classification.SegmentFullJacquetProof`);
  `SegmentHeadJacquetFormula`;
  `SegmentSocleJacquetFormula`;
  `SegmentSpecialJacquetExponentNormFormula`; and clauses (b), (d), (e), (f)
  of the six statements of `Classification.SegmentSocleDerivativesStatement`.
- The additional source and general-input restrictions: no Ze80 §3.5 or §9.6
  segment derivative formula, §4.2 or §9.7 product irreducibility criterion,
  §9.3 analytic or square-integrability result, classification or exhaustion
  theorem is used. No BZ77 derivative theorem, general derivative functor
  result, exactness, Leibniz filtration, geometric lemma, cuspidal support,
  finite-length, tensor, or top-localization theorem is used. In particular,
  no unproved general derivative input or consumer-supplied replacement
  assumption enters the construction. The group name `plusSubgroup` does
  not occur, and no plus-functor result is used.

## Validation boundary

The module compiles with Lean 4.34.0 and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The development check has zero errors and warnings.
