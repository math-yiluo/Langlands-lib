# Canonical regular-tensor contraction statements

Worker 185 states the comparison in David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.2.3,
formula (I.2.3.3), printed page 17 / PDF page 23. The entry module is
`Langlands.Algebra.RegularTensorContractionStatements`; its closed proposition
is `Langlands.Algebra.RegularTensorContractionTheorem.{uA,uM,uN}`.
The main comparison is stated, with no proof in this unit.

## Source and generalization

The governing original is registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant conventions are printed pages 5–7 / PDF pages 11–13.
I.2.1–I.2.3, printed pages 14–18 / PDF pages 20–24, supplies the tensor,
bimodule and contraction setting. Formula (I.2.3.3) identifies the tensor with
the nondegenerate part for an arbitrary ambient module, and identifies it
with the entire module only when that module is nondegenerate.

Renard's displayed lemma assumes an idempotented complex algebra. This file's
arbitrary idempotented `NonUnitalRing` and additive-group formulation is an
internal generalization using the published original-module constructions.
It neither supplies nor assumes a complex vector-space structure on the
ambient module. Explicit original-action inverse maps, the formula for every
fixing idempotent, and whole-map naturality are intrinsic packaging of the
canonical comparison. They are not additional quotations from the source.
No coefficient linearity for a degenerate ambient module is claimed.

The supplementary registered `renard-2010-corrections-complements`, content
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was consulted. Its induction-adjunction and corner corrections
do not alter this contraction assertion. It is supplementary to the governing
2026 version. No dedicated errata note for the governing source was present
in the supplied Library notes or registered source index at the source audit.

## Actual constructions

All short names in the following paragraphs lie in
`Langlands.Algebra.RegularTensorContraction`. Their arguments include the
specified original ring, additive group and `NonUnitalModule` structures.

`Tensor A M` is exactly `NonUnitalModuleTensor.Tensor A A M`, with first factor
carrying `NonUnitalModule.rightRegular A` and second factor carrying the original
action on `M`. Its carrier is in `Type (max uA uM)`. `tensorGroup A M` is the
published inherited additive group. `pure A M` is the actual published `tmul`
for these structures. These are aliases, with no new quotient construction.

`tensorModule A M` is exactly the published one-sided
`NonUnitalBimoduleTensor.leftModule`, using `NonUnitalModule.regular A`,
`rightRegular A` and `regular_actionsCommute A`. This fixes the residual left
action on the tensor. A competing group or action on that carrier is never an
argument of the comparison interfaces.

`contraction A M` is the existing `NonUnitalModuleTensor.lift A` applied to
`(NonUnitalModule.toEndHom originalAction).toAddMonoidHom`. The small helper
`action_balanced` proves its balancing condition by action associativity,
`(a * b) • m = a • (b • m)`, with the original right regular action. This
helper constructs the lift; it does not prove the comparison.

`Forward A M hA` and `Inverse A M hA` abbreviate actual
`NonUnitalModuleHom A` maps between this tensor with its specified residual
action and `nondegeneratePart hA M` with its inherited group and original
action. The part and its inclusion are the published `NonUnitalSubmodule`,
not replacement carriers or a unitized module.

## Proposition interfaces

`Properties A M hA` conjoins the pure formula
`contraction A M (pure A M a m) = a • m`, original-action equivariance,
injectivity, and equality of the contraction's additive range with
`(nondegeneratePart hA M).toAddSubgroup`.

`IsComparison A M hA F G` asserts that composing the entire additive map of
`F` with the actual part inclusion gives the contraction. It also asserts both
complete bundled identities `G.comp F = id` and `F.comp G = id`.
For every `m` in the actual part and every `e : Idempotent A` fixing `m.val`,
it requires `G m = pure A M (e : A) m.val`. Thus the same inverse must work
for every fixing idempotent; no chosen idempotent is a parameter.
`HasComparison A M hA` asserts existence of both such original module maps.

`NondegenerateComparison A M` spells out corresponding original module maps
between the same tensor and the entire ambient `M`, with the forward additive
map equal to the contraction, both full inverse identities, and the same
all-idempotent inverse formula. `ModuleComparison A M hA` conjoins
`Properties`, `HasComparison`, and the implication from the original
`IsNondegenerate A M` to `NondegenerateComparison`. There is no premise of
nondegeneracy on a general ambient module.

For an actual `f : NonUnitalModuleHom A M N`, `tensorMap A f` is exactly
`NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ A) f`, with the same
right regular action on the first factor. `ContractionNaturality A f` is
equality of the entire additive composites
`c_N.comp T(f) = f.toAddMonoidHom.comp c_M`.
`ComparisonNaturality A hA f` quantifies over any comparison witnesses for
`M` and `N` and asserts both whole-map naturality equations. They use the
actual `NonUnitalModuleHom.restrictNondegeneratePart hA f` in the forward
and inverse directions.

The closed `RegularTensorContractionTheorem` universally quantifies `A` and
`hA`. It asserts `ModuleComparison` for every original module in `uM`, asserts
it again for every original module in the independent universe `uN`, and
asserts both naturalities for every original intertwiner between those
universes. The separate existence clauses prevent witness naturality from
being vacuous. There is no comparison, inverse, tensor nondegeneracy,
unitality, commutativity, nontriviality, dimension or countability certificate
among its premises.

## Checks and proof boundary

`RegularTensorContractionChecks` checks full unapplied types, exact unfoldings,
independent and unequal universes, original structures in the presence of
competitors, zero rings, the zero integer action on a nonzero ambient group,
and the regular integer action. Its paired Markdown describes the boundary
examples. These are interface checks, not a proof of the closed target.

For the separate proof, the source's injectivity argument takes a finite sum
of pure tensors and a common left unit for its regular first factors.
Balancing rewrites that sum as the pure tensor of the common unit and the sum
of action values. This is proof-route guidance, never an input certificate
in the statement. The general tensor nondegeneracy theorem is not assumed.

Formula (I.2.3.4), completion comparisons, actual forgetful or pseudo-forgetful
functors, induction adjoints, coefficient refinements, general tensor
nondegeneracy, associativity, Hom adjunction, exactness and corner equivalences
are outside this unit.
