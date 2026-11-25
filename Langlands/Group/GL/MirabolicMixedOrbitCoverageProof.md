# Proof of mixed mirabolic two-orbit coverage, with the open orbit first

The elementary prescribed-row and
nonzero-row proofs adapt the local matrix construction in
`Langlands.Group.GL.MirabolicOppositeProductProof`. That module and its orbit/product theorem are
not imported or used as mathematical premises.

The theorem
`Langlands.GeneralLinear.Mirabolic.MixedOrbit.mirabolicMixedOrbitCoverage`
proves exactly the published proposition
`Langlands.GeneralLinear.Mirabolic.MixedOrbit.MirabolicMixedOrbitCoverageStatement`.
Its complete type is

```lean
{p : ℕ} → [Fact p.Prime] →
  (F : Langlands.PadicField.{uF} p) → (T : F.TopologicalData) →
  Langlands.GeneralLinear.Mirabolic.MixedOrbit.MirabolicMixedOrbitCoverageStatement F T
```

There is only the field universe `uF`. The theorem has no orbit, topology,
representation, character or finiteness premise beyond the field and its
supplied `TopologicalData`. It proves both conjuncts for every `k r : ℕ`,
including both boundary cases. The published target pair and its complete
import closure are unchanged.

## Source and scope

The original geometric assertion is Bernstein–Zelevinsky (1977), *Induced
representations of reductive p-adic groups I*, §7.2, printed p.471, one-based
PDF p.32. The mixed subgroups are §4.12(II),(III), printed pp.456–458,
PDF pp.17–19. Registered source: `bernstein-zelevinsky-1977-induced-i`;
retained PDF:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`;
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The statement development read those passages and their page images; proof
development reread §7.2 and its page image. The statement's bounded search
found no BZ77-specific erratum in the supplied literature and note filenames.
No source citation is treated as a proved Lean input.

The implemented argument is an elementary inverse-row construction. It does
not use an induction comparison, coefficient computation, stabilizer-to-stages
containment, geometric-lemma proof, exactness or derivative theorem from the
same source. The ordered-double-coset packaging is an internal translation
of the source's two complementary orbits.

## The common matrix argument

Work over a field `R` in ambient group `G = mirabolic (t+1) R`. The projection
`projection : G →* GeneralLinear (t+1) R` is the actual upper-left block.
The right acting subgroup is exactly `plusSubgroup t R`: its projected
last row is the delta row at `Fin.last t`. Write

```text
v(g) = last row of projection(g⁻¹).
```

For a cut `s<t`, `Coverage.UpperHead s A` says that the matrix `A` has zero
entries in rows strictly greater than `s` and columns at most `s`.
`Coverage.ZeroHead s v` says that the coordinates at most `s` of `v` vanish.
These are Prop-valued definitions. The auxiliary definition `inverseRow`
is the concrete function `v(g)`.

The common argument takes an actual subgroup `H ≤ G` and proves the orbit
assertion from two entrywise properties: every `projection h`, `h∈H`, is
upper at the cut, and every upper matrix `A` has `levi A∈H`. These properties
are proved for both published subgroups in the accompanying helper module;
they are not hypotheses of the final theorem.

1. **The quotient criterion.** `orbit_iff_row` proves
   `quotientMap H g ∈ cosetOrbit H Q w` if and only if there exists `h∈H`
   whose matrix `projection(w*h)` has last row `v(g)`. In the forward
   direction, quotient equality yields `h = w⁻¹*q*g⁻¹ ∈ H`; the equality
   `w*h = q*g⁻¹` and the defining last row of `q∈Q` give the row formula.
   Conversely set `q=w*h*g`. Its projected last row is
   `v(g)*projection(g)=e_last`, so `q∈Q`. Since `w⁻¹*q=h*g`, its quotient
   class is `H g`. The proof uses `QuotientGroup.rightRel_apply`, whose
   relation is `y*x⁻¹∈H`, with the required equality orientation explicitly.
2. **Upper matrix construction.** Given `v` with nonzero pivot `v p`, replace
   row `p` of the identity by `v`, then swap rows `l,p`. The resulting row
   at `l` is `v`. `Matrix.det_updateRow_sum` computes the first determinant
   as `v p`; `Matrix.det_permute` multiplies by the swap sign. Hence
   `mkOfDetNeZero` produces an actual invertible matrix. If `l,p` are both
   in the head, it is upper. If both are in the tail and the head of `v`
   vanishes, it is upper as well. The lower-left zero proof handles the
   prescribed row, the other swapped row, and all unchanged rows separately.
3. **The identity orbit.** Every row of an invertible matrix is nonzero,
   by the diagonal entry of `A*A⁻¹=1`. If `v(g)` has zero head, choose a
   nonzero tail pivot and prescribe it at the final row. Its Levi lift and
   the quotient criterion place `H g` in the identity orbit. For necessity,
   zero head is preserved by multiplying a row by an upper matrix; applying
   the same fact to the inverse gives an equivalence. The inverse is upper
   because `h⁻¹∈H`. Thus `identity_orbit_iff` identifies this actual orbit
   exactly with zero head.
4. **The cycle orbit.** Suppose the projected last row of `w` is delta at
   `s`. If the head of `v(g)` is nonzero, choose a nonzero head pivot and
   prescribe `v(g)` at row `s`; the quotient criterion gives membership in
   the `w` orbit. Conversely zero-head invariance would make the delta row
   at `s` have zero head, contradicting its entry `1`. Thus
   `cycle_orbit_iff` identifies this orbit exactly with nonzero head.
5. **Actual cover and disjointness.** Quotient induction reduces every
   point to `H g`. The preceding two equivalences and the alternative
   `ZeroHead` or its negation give coverage. Their incompatibility proves
   disjointness of the two actual `cosetOrbit` sets. No enumeration is
   assumed at this step.

## Quotient topology and initial unions

For any Hausdorff topology on `R` with the inherited topological-group
structure on the ambient mirabolic group, every entry of `v(g)` is
continuous: it is the published mirabolic continuous entry map composed
with inversion. The inverse image of the cycle orbit under the actual
quotient map is

```text
⋃ (j : Fin (t+1)) (hj : j.val ≤ s), {g | v(g) j ≠ 0}.
```

Each set is open by `isOpen_ne_fun`, so the union is open. The coinducing
property of `Quotient.mk'` descends this openness to `H \ G`.
`exists_ordered` then constructs an `OrderedDoubleCosets H Q 2` with complete
representative function `![w,1]`: coverage and disjointness are the preceding
proofs, and its three initial unions are empty, the cycle orbit, and the
whole quotient. The latter two endpoint identities use the proved coverage.

The final theorem installs exactly `T.topology`, `T.fieldT2`, and the
published certificate `T.generalLinearTopologicalGroup (k+r+3)` with its
ordinary mirabolic subgroup instance. It never substitutes a canonical
topology or adds continuity/openness hypotheses to the target.

## Specialization and cycle orientation

The helper module `Langlands.Group.GL.MirabolicMixedOrbitSpecializations`
proves, using the actual published rank casts and entrywise subgroup criteria:

| Case | Ambient projection rank | Cut | Upper projections and upper Levi lifts | Projected cycle last row |
| --- | --- | --- | --- | --- |
| Left | `k+r+2` | `s=k` | `leftInducing_projection_upperHead`, `levi_mem_leftInducing` | Delta at `k` |
| Right | `k+r+2` | `s=r` | `rightInducing_projection_upperHead`, `levi_mem_rightInducing` | Delta at `r` |

Here `t=k+r+1`, so `s<t` holds even when `k=0` or `r=0`. The right subgroup's
additional last-column equations hold for the zero-translation Levi lift.
The helper retains every `rankCast`, proves its index equalities using the
published formulas, and computes each cycle row directly from
`descendingCycle_apply_val`. Its paired Markdown gives the full entrywise
proof dependencies.

The final two applications use exactly `leftCycleElement` and
`rightCycleElement`, followed by identity. They obtain equality of the entire
representative function with the respective published function. Since
`cosetOrbit H Q w` is the orbit of `H w⁻¹`, this is the source's open-first
order, with its original descending cycle. Neither cycle is replaced by its
inverse.

## Complete import closure and proof dependencies

The sole direct project import of the proof is the accompanying
`MirabolicMixedOrbitSpecializations`; its sole import is the unchanged
`MirabolicMixedOrbitCoverageStatement`. The remaining complete project
import closure consists of the following 22 published modules (including
the target):

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Maps`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`
- `Langlands.Group.GL.MirabolicMixedOrbitData`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Twist.Definitions`

Every project import edge was traversed. All 44 corresponding Lean/Markdown
files were compared byte for byte with Library base
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb` and are unchanged. The 21 modules
of the statement's earlier dependency audit also retain the hashes recorded
against its original base. The only added import is the fully proved
entrywise helper pair `MirabolicMixedOrbitSpecializations`. Its complete mathematical inputs
are enumerated in its Markdown. The statement's frozen hashes remain
Lean `da09561cad6b79f315a56aa235cc94ea328a0f21c5d9af823e58029414686f0a`
and Markdown `378510114a04fda7f6ac227d39535596fd7ed8bdab69faa46bb59a6332e04bdc`.

The inherited Mathlib imports supply matrix units, determinant and permutation
laws, finite-index arithmetic, ordinary topology and representation definitions.
No additional Mathlib or external module is imported by either new module.
The seven inherited project representation modules define the actual quotient,
`cosetOrbit`, `OrderedDoubleCosets`, support/induction constructions and basic
representation operations. Their construction laws supply no prohibited
representation-theoretic conclusion. In particular, no representation is a
parameter or a proof input here.

| Proof part | Actual mathematical inputs |
| --- | --- |
| Row invariance | Finite matrix multiplication sums, upper zero entries, `Matrix.vecMul_vecMul`, and multiplication/inversion of matrix units. |
| Prescribed row | `Matrix.det_updateRow_sum`, `Matrix.det_permute`, `Equiv.Perm.sign_swap`, `Matrix.GeneralLinearGroup.mkOfDetNeZero`, and identity/swap entry formulas. The adapted helper proof is rechecked locally with its new upper condition. |
| Nonzero row | The diagonal entry of `A*A⁻¹=1`, expanded as a sum. |
| Quotient criterion | Definitions of `LeftQuotient`, `quotientMap`, `cosetOrbit`, `projection`, `plusSubgroup`; `Quotient.exact`, `Quotient.sound`, `QuotientGroup.rightRel_apply`; elementary group cancellation. |
| Identity and cycle orbit criteria | The preceding local lemmas, subgroup inversion, and the explicit projected delta rows. |
| Quotient openness | Published continuous entry maps, group inversion, `isOpen_ne_fun`, unions, and `isQuotientMap_quotient_mk'`. |
| Ordered witnesses | The four defining fields of `OrderedDoubleCosets`, quotient induction, and finite case splitting on `Fin 2`, `Fin 3`. |
| Concrete left/right applications | The six helper adapters listed above; `T.topology`, `T.fieldT2`, and `T.generalLinearTopologicalGroup`. |

Every reused project input is imported from the published Library by Lean
name. The target and concrete data are published Library declarations, as
documented in the helper pair; they fix the types and group constructions
and are not treated as a proved orbit assertion. No lower orbit or
representation theorem is assumed. The code adapted from the published
`MirabolicOppositeProductProof` imports none of its additional closure; the
local statements here are proved directly from the listed matrix laws.

## Results not used


The checks below cover mathematical conclusions and their transitive
dependents as well as the named modules. No theorem proving
any excluded conclusion is imported or used. The helper proofs have exactly the
matrix-entry dependencies listed above; no premise of a later result supplies an
upstream input.

1. **Plus functors and compatibility.** No plus functor, adjunction, BZ77
   4.13(d), general Leibniz proof or derivative compatibility is imported.
   `plusSubgroup` and its elementary matrix maps occur as permitted group
   infrastructure. No derivative functor module is in the closure, and no
   BZ77 derivative conclusion is assumed.
2. **Geometric and analytic comparisons.** No geometric-lemma proof,
   restriction-sequence theorem, exactness, character matching,
   stabilizer-to-stages containment, Haar scaling, integration or induction
   comparison is used. The imported support and induction definitions are
   constructions, not proofs of those comparisons.
3. **Whittaker finiteness.** No `Langlands.Whittaker` module is imported.
   In particular the closure avoids
   `SupercuspidalCoinvariantFinitenessStatement`,
   `IrreducibleCoinvariantFinitenessStatement`,
   `LeviCuspidalCoinvariantFinitenessStatement` and the dependent finite-length
   route. No arbitrary-character or
   degenerate-character finiteness conclusion is used.
4. **Segment-pair structure, commutation and gluing.** The closure has no
   segment, head, socle or Jacquet module. It avoids
   `UnlinkedSegmentSocleProductIrreducible`,
   `LinkedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSoclePairReducible`,
   `JuxtaposedSegmentSocleReverseProductStructure` and
   `LinkedSegmentSocleReverseProductQuotientHom`,
   `SegmentSocleProductIrreducibility`,
   `AdjacentUnlinkedSegmentSocleSwap`,
   `TwoSegmentSocleCommutation` and
   `LinkedSegmentSocleGluing`.
5. **Individual and ordered existence, criteria and exhaustion.** The same
   closure avoids individual special-head/reverse-socle existence, individual
   segment-socle/reverse-head existence,
   `OrderedMultisegmentSocleExistence`, socle exhaustion,
   `SegmentHeadProductIrreducibility`,
   `GenericSegmentProductUniqueness`, multisegment special-head
   exhaustion, ordered strong-head
   existence, quotient coverage and ordered conversion.
6. **Classification and square integrability.** No classification module
   is imported. The closure avoids analytic segment classification,
   `SegmentSpecialEssentialSquareIntegrability`, tempered uniqueness,
   `SquareIntegrableLanglandsClassification`, square-integrable exhaustion
   and regular exhaustion.
7. **Segment derivatives, Jacquet formulas and Ze80.** No segment derivative
   formula, segment existence/Jacquet formula, or segment classification is
   used. The closure avoids `SegmentFullJacquetFormula`,
   `SegmentHeadJacquetFormula`,
   `SegmentSocleJacquetFormula` and
   `SegmentSpecialJacquetExponentNormFormula`.
   Ze80 §§3.5, 9.6, Theorems 4.2, 9.3, 9.7 and classification/exhaustion
   results are not used.
8. **Two-supercuspidal conclusions.** No supercuspidal theorem is imported.
   The closure avoids `TwoSupercuspidalNonadjacentProductIrreducible` and
   `TwoSupercuspidalProductStructure`.
9. **Dependency boundaries.** Unproved statements, citations and
   conditional assemblies are not proved orbit inputs.
   Missing derivative or tensor inputs are not replaced by assumptions
   taken from results that use this theorem.

These exclusions apply to every helper and its
transitive mathematical dependencies. In particular, the statements imported
for types are not theorem assumptions, and no proof or downstream
consequence from an excluded family is used to justify a matrix law.


These checks apply to both files and to the final proof as a whole.
The proof establishes only the mixed two-orbit geometry. The corresponding
coefficient, stabilizer-to-stages, restriction-sequence, exactness,
compatibility and finiteness results are separate.

## Validation

Both modules and the complete theorem compiled in the pinned environment
(Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Declaration inspection confirms
that the theorem has only universe `uF` and the axiom closure
`propext`, `Classical.choice`, `Quot.sound`.
