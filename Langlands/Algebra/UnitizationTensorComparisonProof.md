# Renard I.2.1: proofs of the unitized tensor comparison and the unitization uniqueness

Module `Langlands.Algebra.UnitizationTensorComparisonProof`.
Namespace `Langlands.Algebra.UnitizationTensorComparison`.
Main theorem `statements : Statements.{uK, uA, uX, uY}`.

Worker 132 prepared this submission from the complete proof in shared draft
revision 2 of task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The task context
attributes that draft to coauthor Worker 1222; the draft's original Markdown
credits Worker 14. The Lean proof is unchanged from that draft. Worker 132
checked it against the current published statement and updated this provenance.

It proves the four propositions of
`Langlands.Algebra.UnitizationTensorComparisonStatements` without changing that
module or its dependencies. The source is David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, I.2.1, printed
p.14 / PDF20, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
See the statement module's Markdown for the source correspondence and the
integer-span convention. The proof below is an internal derivation from the
published constructions.

## Theorems

| Theorem | Proves |
| --- | --- |
| `scalarQuotientComparison` | `ScalarQuotientComparisonStatement` |
| `nondegenerateUnitizedTensor` | `NondegenerateUnitizedTensorStatement` |
| `unitalUnitizedTensor` | `UnitalUnitizedTensorStatement` |
| `unitizationAlgebraUnique` | `UnitizationAlgebraUniqueStatement` |
| `statements` | `Statements`, the conjunction of the four |

## Proof of (i): `ker q = H` and `qbar` is bijective

The section `Kernel` fixes `k`, `A`, `X`, `Y` with the instances of the statement.
Write `TA` for the original balanced tensor, `TU` for the tensor over
`Unitization k A`, `H` for `scalarRelations` and `Q = TA ⧸ H` for
`ScalarQuotient`.

1. `quotientBiadditive : X →+ Y →+ Q` sends `(x, y)` to the class of
   `tmul x y`. It is the published `NonUnitalModuleTensor.biadditive`
   post-composed (`AddMonoidHom.compr₂`) with the quotient map.
2. It is balanced for the original action (`quotientBiadditive_isBalanced`), by
   `NonUnitalModuleTensor.tmul_balanced`. It is balanced for the scalars
   (`quotientBiadditive_isScalarBalanced`), because each difference
   `tmul (c • x) y − tmul x (c • y)` lies in `H` (`scalarDifference_mem`).
3. The published universal property of `TU`, `unitizedLift`, turns it into
   `inverse : TU →+ Q`, with `inverse (unitizedTmul x y) = [tmul x y]`.
4. `descendedComparison_inverse`: `qbar ∘ inverse` is the identity of `TU`. The
   two maps agree on pure tensors by definition, so `unitizedHom_ext` applies.
5. `inverse_descendedComparison`: `inverse ∘ qbar` is the identity of `Q`. Every
   class is `[t]` for some `t : TA`, so it suffices that
   `inverse ∘ q = H.mkQ` as additive maps `TA →+ Q`
   (`inverse_comp_comparison`). This holds on pure tensors by definition, so
   `NonUnitalModuleTensor.hom_ext` applies.

`scalarQuotientComparison` then concludes:

- Bijectivity of `qbar` follows from steps 4 and 5
  (`Function.bijective_iff_has_inverse`).
- `H ≤ ker q` is the published `scalarRelations_le_ker`. Conversely, if
  `q t = 0` then `qbar [t] = 0`, so `[t] = inverse (qbar [t]) = 0` by step 5,
  that is, `t ∈ H` (`Submodule.Quotient.mk_eq_zero`).

## Proof of (j): the canonical-scalar comparison is bijective

`nondegenerateUnitizedTensor` installs the published canonical scalars and their
compatibility proofs as in the statement. Surjectivity is the published
`comparison_surjective`. For injectivity:

- `H = ⊥`. By `Submodule.span_eq_bot`, it suffices that every generator
  `tmul (c • x) y − tmul x (c • y)` vanishes. This is the published
  `NondegenerateTensorScalars.tmul_smul_left_eq`, which moves canonical scalars
  between the factors using a fixing idempotent and original balancing.
- If `q s = q t`, then `s − t ∈ ker q`. By part (i), applied to the canonical
  scalar structures, `ker q = H = ⊥`, so `s = t`.

## Proof of (k): the unital case

`unitalUnitizedTensor` applies `nondegenerateUnitizedTensor` with
`IsIdempotented.of_ring R` and `isNondegenerate_iff_isUnitalModule.mpr` for both
factors. The statement's unital canonical scalars
`NondegenerateScalars.unitalModule` are by definition the canonical scalars at
these arguments, so the instance terms agree definitionally. Mathlib's
`Algebra k R` supplies the module, scalar-tower and commuting instances on `R`.

## Proof of (f): the algebra structure on the unitization

`unitizationAlgebraUnique` proves the existence clauses from Mathlib's ring
structure on `Unitization k A`: `mul_assoc`, `one_mul`, `mul_one` and
`Unitization.inr_mul`.

For uniqueness, let `μ` be `k`-bilinear with `μ 1 u = u`, `μ u 1 = u` and
`μ a b = a * b` on `A`. First, `inl r = r • 1` (checked on both coordinates).
By `LinearMap.ext₂` it suffices to compare `μ u v` with `u * v`. Write
`u = inl u.1 + u.2` and `v = inl v.1 + v.2`
(`Unitization.inl_fst_add_inr_snd_eq`) and replace each `inl` by a multiple of
`1`. Bilinearity of `μ` and of `LinearMap.mul` expands both sides into four
terms. The unit hypotheses and `one_mul`/`mul_one` evaluate the terms that
involve `1`, and the hypothesis on `A` with `Unitization.inr_mul` evaluates the
remaining term. One `simp only` call closes the goal. No associativity of `μ` is
used.

## Dependencies

Imports only `Langlands.Algebra.UnitizationTensorComparisonStatements`. The
universes `uK uA uX uY` are independent, and no hypothesis beyond those of the
statements is added. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
