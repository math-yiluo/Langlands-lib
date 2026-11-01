# Arbitrary base change of the global normalized Harris determinant locus

Author: Worker 344.

This internal construction proves that the actual global closed determinant
locus in a supplied family commutes with arbitrary base change. The arithmetic
data, normalized Harris signature charts, conjugated reflex scalar map, actual
abelian scheme and rational algebra action are exactly those of
`HarrisTaylorCMDeterminantGlobal`. The schemes and arithmetic types have
universe zero. There is no additional `IsCMField F`, division, affineness,
flatness, reducedness, Noetherian or global Lie freeness hypothesis.

Write `Z → S` for the constructed closed locus of an actual family `B/S`
with action `i` and structure map `p : S → Spec F`. For any actual
`b : T → S`, form the actual family `(baseChange b).obj B`, the actual
action `(rationalBaseChangeEnd b B).comp i`, and their independently
constructed determinant locus `Zₜ → T`. The main theorem
`harrisTaylorCMGlobalDeterminantBaseChange_isPullback` proves the square

```text
Zₜ ───────────→ Z
│               │
↓               ↓
T ───── b ────→ S
```

is cartesian in the category of actual schemes. The horizontal map is the
constructed `harrisTaylorCMGlobalDeterminantBaseChangeMap`. Consequently
`harrisTaylorCMGlobalDeterminantBaseChangeIso` is an actual scheme
isomorphism `Zₜ ≅ pullback b ι`; its two projection equations are proved.
Both constructions use the full existing normalized determinant condition,
including every finite order family, every finite Lie chart, and every
smaller open in actual structure-sheaf section rings.

The implemented proof first converts the universal family's determinant
condition to the existing class-based test-map property. For any test map
satisfying that property, `harrisTaylorCMGlobalDeterminantLift` chooses its
factorization through `Z`, using the proved global factorization criterion.
Its inclusion equation is the chosen factorization equation. Cancellation
against the closed inclusion proves uniqueness, and the same cancellation
shows that lifts commute with arbitrary precomposition of test maps.
Thus the choices do not introduce an ambiguity in the resulting morphisms.

The universal inclusion `Zₜ → T` satisfies the determinant property for the
actual pulled-back family. The existing
`harrisTaylorCMDeterminantPullbackCondition_baseChange_iff` identifies this
with the property of its composite into `S`. Lifting that composite
constructs the horizontal map and proves commutativity.

For a cone over `T → S ← Z`, precomposition stability gives the determinant
property of its map into `S`, since it factors through `Z`. Commutativity
and the same actual-family base-change equivalence give the determinant
property for its map into `T`. Its unique factorization through `Zₜ`
is the cone lift. The first projection equation is that factorization
equation; cancellation against `Z → S` proves the second. Cancellation
against `Zₜ → T` proves uniqueness. These are the complete pullback
universal properties used to construct the comparison isomorphism.

The provenance is internal. This module derives its results from the actual
closed determinant loci, their full test-map factorization criteria, the
proved rational-action class composition identity and determinant
precomposition stability. Mathlib's `PullbackCone.IsLimit.mk` and
`IsPullback.isoPullback` package the proved universal property. It assumes
no external moduli existence assertion.

The conclusion concerns determinant loci in supplied actual families and
their base changes. Ambient polarized moduli existence, polarization and
Rosati compatibility, rational-isogeny and level-orbit comparisons,
admissibility, smoothness, projectivity, and the natural normalized moduli
comparison in `DivisionCMRepresentabilityStatement` remain separate
obligations.
