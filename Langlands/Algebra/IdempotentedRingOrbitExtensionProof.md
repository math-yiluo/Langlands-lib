# Uniform continuity and unique continuous extension of actual orbit maps

Author: Worker 345.

`Langlands.Algebra.idempotentedRingOrbitExtension.{uA,uM}` proves exactly
`Langlands.Algebra.IdempotentedRingOrbitExtensionTheorem.{uA,uM}` from
`Langlands.Algebra.IdempotentedRingOrbitExtensionStatements`. The ring and
module universes are arbitrary and independent. The theorem adds no hypotheses
to the published statement and leaves its Lean/Markdown dependency closure
unchanged.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.2, printed p.7/PDF13, gives finite upper bounds for idempotents and defines
nondegeneracy by the existence of a fixing idempotent for every vector.
I.1.3, printed pp.8–9/PDF14–15, constructs the actual right-coordinate
uniformities and the canonical compatible family of an original scalar.
The last paragraph of I.1.3, printed p.9/PDF15, gives the extended action
`x(e) • m` whenever `e • m = m` and asserts that the original uniformly
continuous orbit extends continuously to the compatible-family space.

PDF13–15 were read for this proof, and PDF15 was also inspected visually.
No source-specific errata note was found in the project. The supplementary
registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF1–3. Its first page corrects the old pseudometric inequality
and a fixed-point formula; the governing 2026 text contains the corrected
formulas. These corrections do not change the orbit extension paragraph.

The original orbit's uniform continuity, the extended orbit's continuity,
and its canonical restriction implement that paragraph. Uniform continuity
of the extended orbit and uniqueness among all continuous extensions are
internal consequences, as recorded in the published statement Markdown.
The direct uniqueness argument below uses the canonical-point approximation
in the source's density argument on PDF15. It proves the needed approximation
inside this proof and does not import or assume the separate density or
completeness theorem.

## Exact objects and scope

The hypotheses are `NonUnitalRing A`, `AddCommGroup M`,
`NonUnitalModule A M`, `IsIdempotented A`, and `hM : IsNondegenerate A M`.
The original orbit is `a ↦ a • m` for the given original action. Its domain
uniformity is exactly `idempotentedRingUniformSpace A`.

The extended orbit is exactly
`x ↦ IdempotentedRingRightLimitAction.act hM x m` on the published actual
compatible-family carrier `IdempotentedRingRightLimit A`. Its domain
uniformity is exactly `IdempotentedRingRightLimit.uniformSpace A`. Both
codomains use `(⊥ : UniformSpace M)`, whose topology is the discrete topology
on the original additive carrier. The proof supplies all uniformities
explicitly when composing uniformly continuous functions and when deriving
continuity. For uniqueness it installs those same structures locally.

The competitor is an arbitrary function `f : IdempotentedRingRightLimit A → M`
continuous for these topologies and agreeing with `a • m` on every canonical
scalar. There is no additive, equivariant, or uniform-continuity assumption
on `f`. No global unit, original unit-action law, nontriviality, commutativity,
field, countability, or dimension condition occurs. In particular zero rings
and trivial carriers are included.

## Implemented proof

First, `hsmul` proves that `a ↦ a • m` is uniformly continuous when its
*domain* has the discrete uniformity. The criterion
`uniformContinuous_iff_le_comap` reduces this to `bot_le`; this auxiliary
fact does not assert that the actual original-ring uniformity is discrete.

For `horiginal`, choose `e` with `(e : A) • m = m` using `hM m`.
The published `idempotentedRing_uniformContinuous_rightCoordinate e` maps
the actual original-ring uniformity to discrete `A` by `a ↦ a * e`.
Compose it with `hsmul m`. Associativity of the original action and the
fixing equation give `(a * e) • m = a • m`, yielding exactly
`IdempotentedRingOriginalOrbitUniform A M`.

For `hextended`, choose a fixer `e` again. The published `act_eq hA hM`
identifies the actual orbit pointwise with `x ↦ x.val e • m`.
The published `uniformContinuous_coordinate e` maps the actual family
uniformity to discrete `A` by `x ↦ x.val e`. Composition with `hsmul m`
therefore proves exactly `IdempotentedRingRightLimitOrbitUniform A M hM`.
`UniformContinuous.continuous` supplies continuity with the required
topologies, and the published `canonical_act hA hM a m` supplies canonical
restriction to the original action.

For uniqueness, fix a continuous competitor `f` with the required canonical
restriction, a vector `m`, and a family `x`. Continuity into discrete `M`
gives `f y = f x` for all `y` in a neighborhood of `x`. The published
`nhds_hasBasis hA x` supplies an idempotent `d` such that equality of the
`d` coordinate implies this equality of values. Choose `e` fixing `m`, and
use `hA.finite_upper_bound {d,e}` to choose `g` above both. The published
`Idempotent.smul_eq_of_le` gives `(g : A) • m = m`.

Consider `y = canonical (x.val g)`. Its `d` coordinate is
`x.val g * d`, which equals `x.val d` by the defining compatibility
`x.property.2 d g hdg`. Thus `f y = f x`. Canonical restriction gives
`f y = x.val g • m`, while `act_eq` at the fixer `g` identifies the latter
with `act hM x m`. Consequently `f x = act hM x m`; function extensionality
proves the required equality for every `f`. No density, extension,
uniqueness, or continuity premise remains in the closed theorem.

## Checks and boundaries

The Lean file includes complete unapplied checks of the closed proof at
arbitrary independent universes and at both unequal assignments `(0,1)` and
`(1,0)`. Development compilation is separate from the independent validation,
semantic review, and publication required for acceptance.

The proof concerns only the two orbit maps and uniqueness of their continuous
extension. Uniform completion equivalences, multiplication continuity,
categorical module equivalences, and the module completion in I.1.4 remain
outside this result.
