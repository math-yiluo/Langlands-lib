# Actual rational-character norms, integer valuation and real logarithm

This unit composes the published group-scheme rational-character evaluation
with the published unrestricted local-field norm and order. All maps refer
to the actual characters and rational points of the given group scheme.

The source conventions are Waldspurger 2003, I.1, printed pp.238–240
(PDF pp.4–6), registered as `waldspurger-2003-plancherel`, and Renard's
9 July 2026 edition, V.1–V.2.3, printed pp.103–106 (PDF pp.109–112),
registered as `renard-2026-representations-groupes-reductifs-padiques`.
Waldspurger defines `Rat(G)`, the common norm kernel and the real logarithm,
with the explicit convention
`q ^ (−⟨χ,H_G(g)⟩) = |χ(g)|_F`.
Renard defines the integer-dual-valued map by `v_F(χ(g))`, its kernel
and its actual image, and displays the associated exact sequence.

The derived generalization here is to any group scheme over the local
field. The algebraic composition and its intrinsic laws do not require
reductivity, connectedness or affineness. No assertion about a finite-rank
character lattice, the real dual of a split central torus, or rational-point
topology is inferred in this wider setting.

## Inputs and reused objects

Let `F : Type u` have the published instances `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`, and let
`G : Langlands.GroupScheme (Spec (CommRingCat.of F))`.
There is no restriction on the characteristic and no finite-extension-of-ℚₚ
assumption. The field and scheme universe follows the shared group-scheme
interface; no representation carrier is involved.

The construction imports and uses these existing objects without replacing
their definitions:

- `GroupScheme.rationalCharacters G`, the actual algebraic homomorphisms
  into `𝔾_m` defined over `F`, written additively.
- `GroupScheme.rationalPoints G` and `rationalCharacterEvalHom`, the actual
  point group and additive family of evaluation homomorphisms into `Fˣ`.
- `fieldNormUnits F`, the units restriction of
  `LocalField.residueNormalizedAbsoluteValue F`.
- `fieldOrderUnits F`, whose integer coordinate equals `FML.ord` on units,
  with the positive order convention.
- `evaluationNormCharacters`, `characterValuation`, their actual-image
  and quotient constructions, and `normLogarithm`.

## Constructions and exact laws

All declarations below are in `Langlands.Plancherel`.

`rationalNormCharacters G` composes the actual evaluations with
`fieldNormUnits F`. Its `_apply` and `_val` lemmas give the units formula
and identify its real value with `|χ(g)|_F`.

`rationalCharacterValuation G` composes the same evaluations with
`fieldOrderUnits F`. The `_apply` lemma identifies each integer coordinate.
The `_ord` lemma states that its cast into `WithTop ℤ` equals the existing
`FML.ord` of the nonzero character value.

`rationalCommonNormKernel G` is the previously defined `commonNormKernel`
of this actual family. It is normal. `mem_rationalCommonNormKernel` gives
the simultaneous norm-one condition.
`rationalCharacterValuation_ker` proves equality with the kernel of the
actual integer-valued map; it applies the already proved
`fieldNormUnits_eq_one_iff`, with no extra compatibility hypothesis.
`mem_rationalCommonNormKernel_iff_valuation` gives the equivalent simultaneous
zero-coordinate condition.

`rationalNormLogarithm G` is `normLogarithm` with this actual norm family and
the actual residue cardinality `q`.
`rationalNormLogarithm_spec` proves the source's exponential identity.
`rationalNormLogarithm_eq_intValuation` identifies every real coordinate
with the cast of the corresponding integer coordinate. Its proof discharges
the generic numerical normalization premise using `fieldNormUnits_rpow`,
and obtains `q > 1` from `LocalField.residueCardinality_gt_one`.
`rationalNormLogarithm_ker` proves equality with the same actual norm kernel.

`rationalCharacterValuationImage G` is the actual range subgroup in the
integer dual, not a chosen lattice. `rationalNormKernelQuotientEquiv G`
is the canonical algebraic multiplicative equivalence
`G(F)/G(F)¹ ≃* image(H_G)`, obtained from the existing first-isomorphism
construction and the proved equality of kernels. Its `_mk` lemma sends
the class of `g` to the valuation of `g`, bundled in the actual image.

`commutator_le_rationalCommonNormKernel` proves containment of the abstract
group commutator subgroup, by the abelian target of the valuation.
It asserts no comparison with rational points of an algebraic derived group.

For every group-scheme morphism `f : H ⟶ G`,
`rationalNormCharacters_characterRestrict`,
`rationalCharacterValuation_characterRestrict` and
`rationalNormLogarithm_characterRestrict` identify the restricted coordinate
at `y` with the original coordinate at `rationalPoints.map f y`.
The first two follow from actual evaluation compatibility; the last uses
the proved integer-coordinate comparison.

## Scope retained for later work

This is an actual algebraic specialization of the generic norm, valuation
and logarithm constructions. It also applies when the rational-character
group is trivial. It does not provide a topology on `G(F)`, continuity or
local constancy of evaluation or norms, open or closed common kernels,
compact-subgroup containment, an algebraic derived-point comparison,
unimodularity, finite generation or full rank of the image, finite index
of the split-center image, a scalar-extension identification with
Waldspurger's `a_G`, complex or unitary character tori, or Haar measures.
Those obligations remain separate, including for connected reductive groups.
