# Normalizer shifts on original field points

This internal unit isolates the exact normalizer-shift input needed after
restriction of a root-function family along a field extension. It uses the
existing rational points, character pullback, normalizer-point extension and
literal `RootFunctionFamily.fieldRestrict`. No complete valuation over the
larger field is assumed.

For a monomorphic map `i : S.toGrp ⟶ G` with `G` affine, suppose a family
`φ` is top on nonroots and outside the actual root group for each root.
`smul_eq_vadd_iff_on_rootGroups` says that `n • φ = v +ᵥ φ` is equivalent
to its value formula on the original actual root groups. The forward
implication evaluates the equality. In the reverse implication, the supplied
formula handles points in root groups. Conjugation by the normalizer
preserves root-group membership, and its Weyl action preserves the root set,
so support normalization handles every other point.

For fields `k → K` in an arbitrary universe, `fieldRestrict_normalization`
descends these two normalization laws. Its additional assumptions are that
`G` is smooth and `S` is split. The actual root-support comparison and the
fpqc reflection of nonzero root-group membership supply the proof. It does
not require reflection, opposite-root or other valuation axioms.

Write `ψ` for any upstairs family for `S_K` in `G_K`, `a_K` for actual
character base change and `g_K` for actual rational-point extension.
Assume only the two support-normalization laws for `fieldRestrict ψ`.
`fieldRestrict_smul_eq_vadd_iff` proves the exact equivalence

```text
n • fieldRestrict ψ = v +ᵥ fieldRestrict ψ
  iff
for every original root a and g ∈ U_a(k),
  (n_K • ψ)(a_K, g_K) = ψ(a_K, g_K) + coe(eval S a v).
```

This uses the existing unconditional normalizer equivariance of literal
field restriction and the first equivalence. The test points are extensions
of the original field's points. No formula is requested at other `K`-points.
No splitness or smoothness assumption is needed for this equivalence when
the two normalization laws downstairs are already supplied.

`fieldRestrictNormalizerShift` chooses a vector from the existential
original-point formula for one supplied original normalizer. Its dependent
pair retains the equality of complete families over `k`.

Finally, `fieldRestrict_reflection_of_originalPointShifts` derives exactly
the existing V2 conclusion from these shifts for every original normalizer.
For a normalizer realizing reflection in `a`, evaluate the chosen
whole-family equality at `(-a, n * g * n⁻¹)`. The inverse Weyl action sends
`-a` to `a`, inverse conjugation cancels, and the reflection constant is
`-eval S a v`. The conclusion has all original root, normalizer,
root-group and nonidentity quantifiers.

These are internal consequences of the existing family actions and field
restriction interfaces. The pointwise shift formula is an explicit premise,
equivalent to the desired original-family shift; it is not established for
a new class of groups. In particular this unit neither constructs an
adapted upper apartment nor imposes covariance on every point of a
nonmaximal torus centralizer over `K`. Initial and adapted existence,
opposite V5, the metric building and the original supplied-model
special-vertex comparison remain open. The unchanged
`IntegralModel.BuildingComparisonStatement` is not proved here.
