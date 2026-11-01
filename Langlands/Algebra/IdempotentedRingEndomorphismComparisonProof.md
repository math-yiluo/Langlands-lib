# Proofs of the comparison and closure targets for the right-linear model

Authors: Worker 1170 (Lean proof and Markdown) and Worker 1126 (recheck
against the published statement and Markdown revision).

This module proves the five component targets of
`Langlands.Algebra.IdempotentedRingEndomorphismComparison` (Worker 1126) and
their aggregate. It changes nothing in the statement module or its imports.
The final theorem is

```
Langlands.Algebra.idempotentedRingEndomorphismComparisonTheorem_proof :
  IdempotentedRingEndomorphismComparisonTheorem.{uA}
```

for an arbitrary universe `uA`. Its only hypotheses are those inside the
statement: an original `NonUnitalRing A` and `IsIdempotented A`. It has no
extra hypothesis. `lean_check` reports the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The source is Renard, *Représentations des groupes réductifs p-adiques*
(2026), I.1.4 remark, printed p.10/PDF16, and I.1.6, printed
pp.11–12/PDF17–18. The statement Markdown records the provenance of each
target. The proofs below follow the source's arguments where it gives them.
Where the source says "il est clair" or "bien sûr", they supply the omitted
steps.

## Imports

- `Langlands.Algebra.IdempotentedRingEndomorphismComparison`, the target
  statements.
- `Langlands.Algebra.IdempotentedRingTopologyProof`, for the published proofs
  `idempotentedRing_hausdorff` and
  `idempotentedRing_rightMultiplicationUniform` about
  `idempotentedRingUniformSpace A`.

Every other lemma used is either published (in
`IdempotentedRingEndomorphism`, `IdempotentedRingRightLimitRing`,
`IdempotentedRingRightLimitUniformity`, `IdempotentedRingUniformity`,
`IdempotentedRing`) or from Mathlib.

## Helper lemmas

They are in the namespace
`Langlands.Algebra.IdempotentedRingEndomorphismComparisonProof`. Each takes
`{A : Type uA} [NonUnitalRing A]` and `hA : IsIdempotented A`.

- `exists_leftLocalUnit hA a`: some idempotent `e` has `e * a = a`. It comes
  from `IsIdempotented.iff_two_sided_local_units` applied to `{a}`.
- `idempotentEvaluation_toRightLinearEnd hA x`:
  `idempotentEvaluation (toRightLinearEnd hA x) = x`. The proof uses
  coordinate extensionality and the published `toRightLinearEnd_idempotent`,
  which gives `(toRightLinearEnd hA x).val e = x.val e`.
- `toRightLinearEnd_idempotentEvaluation hA β`:
  `toRightLinearEnd hA (idempotentEvaluation β) = β`. Fix `a` and take `e`
  with `e * a = a`. The published `toRightLinearEnd_apply_eq` gives the value
  `β e * a`. Right linearity (`rightLinearEnd_apply_mul`) rewrites this as
  `β (e * a)`, which is `β a`. This is the argument of the I.1.4 proposition,
  printed p.10/PDF16, in its right-module form.
- `comap_toRightLinearEnd_eq hA`: the pullback of
  `rightLinearEndUniformSpace A` along `toRightLinearEnd hA` equals the
  pullback of `functionUniformSpace A` along `applyOriginal hA`. It holds
  because comaps compose (`UniformSpace.comap_comap`) and the composite
  `x ↦ ((toRightLinearEnd hA x).val : A → A)` is definitionally
  `applyOriginal hA`.
- `uniformContinuous_coordinate_of_comap hA e`: `x ↦ x.val e` is uniformly
  continuous from that pullback to the discrete uniformity on `A`. The map
  factors as `x ↦ applyOriginal hA x e * e`. This uses
  `applyOriginal_idempotent` and the compatibility `x.val e * e = x.val e`.
  The factors are three uniformly continuous maps: the comap projection,
  evaluation at `e` on the product, and the published right coordinate
  `idempotentedRing_uniformContinuous_rightCoordinate e` into `⊥`.
- `uniformContinuous_applyOriginal hA`: `applyOriginal hA` is uniformly
  continuous from `IdempotentedRingRightLimit.uniformSpace A` to
  `functionUniformSpace A`. By `uniformContinuous_pi` it suffices to treat one
  value `a`. The codomain uniformity on `A` is the infimum over idempotents
  `f` of comaps along `b ↦ b * f`, so it suffices to treat
  `x ↦ applyOriginal hA x a * f` into `⊥`. This uses `uniformContinuous_iInf_rng`
  and `uniformContinuous_comap'`. With `e * a = a`, `applyOriginal_eq` turns
  this map into `x ↦ x.val e * a * f`. That map is a function of the
  published coordinate `x ↦ x.val e`, which is uniformly continuous into `⊥`
  (`IdempotentedRingRightLimit.uniformContinuous_coordinate e`). Every map out
  of `⊥` is uniformly continuous.
- `comap_toRightLinearEnd hA`: the uniformity comparison for one ring. After
  `comap_toRightLinearEnd_eq`, the two inequalities come from the last two
  lemmas through `uniformContinuous_iff_le_comap`. The family uniformity is
  by definition the infimum over `e` of the comaps of `⊥` along
  `x ↦ x.val e`. So the pullback lies below it exactly when every coordinate
  is uniformly continuous from the pullback. The reverse inequality is the
  uniform continuity of `applyOriginal hA`. This is the source's check on
  PDF17, which uses a local unit `f` with `f a_i = a_i` and
  `Ā(1-f) = O(A(1-f), f) ∩ Ā`, written as uniform continuity in both
  directions.
- `rightLinearEnd_isClosed hA`: the right-linear subset is closed for
  `(pointwiseUniformSpace A).toTopologicalSpace`. As a set it is
  `⋂ a, ⋂ b, {β | β (a * b) = β a * b}`. Each piece is the equalizer
  (`isClosed_eq`) of two continuous maps into `A`. The first is evaluation
  at `a * b` (`uniformContinuous_evaluation`). The second is evaluation at
  `a` followed by right multiplication by `b`, which is uniformly continuous
  by `idempotentedRing_rightMultiplicationUniform hA b`. The codomain is
  Hausdorff by `idempotentedRing_hausdorff hA`. Both inputs need the local
  units.
- `closure_range_leftMultiplication hA`: the closure identity for one ring.
  - `⊆`: every left multiplication is right-linear by associativity, and the
    right-linear subset is closed (`closure_minimal`). This is the source's
    "bien sûr" inclusion.
  - `⊇`: let `β` be right-linear. The idempotents are a directed order: two
    of them have a common upper bound by `IsIdempotented.finite_upper_bound`.
    They are nonempty because `0` is one. Along `atTop` on this order,
    `e ↦ leftMultiplication (β e)` converges to `β`. The pointwise topology
    is induced from the product, so by `Topology.IsInducing.tendsto_nhds_iff`
    and `tendsto_pi_nhds` it suffices to fix `a`. Take `e₀` with
    `e₀ * a = a`. For `e ≥ e₀`, `Idempotent.mul_eq_of_le` gives `e * a = a`,
    so `β e * a = β (e * a) = β a`. The coordinate is therefore eventually
    constant. Every term lies in the range of left multiplication, so
    `mem_closure_of_tendsto` gives `β` in the closure. This is the source's
    "il est clair" inclusion, for which the source prints no argument. The
    directed limit over idempotents is the Lean proof's own route.

## Component and aggregate theorems

They are in the namespace `Langlands.Algebra`.

| Theorem | Target | Proof |
| --- | --- | --- |
| `idempotentedRingEndomorphismInverseIdentities_proof` | `IdempotentedRingEndomorphismInverseIdentities.{uA}` | the two inverse lemmas |
| `idempotentedRingEndomorphismRingEquivalence_proof` | `IdempotentedRingEndomorphismRingEquivalence.{uA}` | see below |
| `idempotentedRingEndomorphismUniformityComparison_proof` | `IdempotentedRingEndomorphismUniformityComparison.{uA}` | `comap_toRightLinearEnd` |
| `idempotentedRingEndomorphismRightLinearClosed_proof` | `IdempotentedRingEndomorphismRightLinearClosed.{uA}` | `rightLinearEnd_isClosed` |
| `idempotentedRingEndomorphismClosureLemma_proof` | `IdempotentedRingEndomorphismClosureLemma.{uA}` | `closure_range_leftMultiplication` |
| `idempotentedRingEndomorphismComparisonTheorem_proof` | `IdempotentedRingEndomorphismComparisonTheorem.{uA}` | the five components |

The ring equivalence is built with `IdempotentedRingRightLimit.ring hA`
installed by `let`, which is the installation the statement uses. Its forward
function is `toRightLinearEnd hA`, and its inverse function is
`idempotentEvaluation`. The inverse laws are the two inverse lemmas.
Multiplicativity and additivity are `map_mul` and `map_add` of the published
ring homomorphism `toRightLinearEnd hA`. The two required equalities of
complete functions then hold by `rfl`.

## Scope

This module proves only the five targets and their aggregate. Natural
endomorphisms of the forgetful functor (printed p.12/PDF18), categorical
centres (I.1.7) and further completion results remain separate obligations.
