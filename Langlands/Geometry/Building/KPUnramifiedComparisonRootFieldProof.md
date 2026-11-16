# The root field for concrete unramified apartment lifts

`Langlands.Geometry.Building.unramifiedComparisonRootField` proves exactly
`UnramifiedComparisonRootFieldStatement.{u}` at arbitrary universe `u`.
It retains every published hypothesis on the field, affine group scheme,
parahoric building data, apartment axioms, special torus and supplied concrete
apartment lift. The proof applies the published
`unramifiedComparisonRootField_of_doubledRootDepthModel` to the published
`unramifiedDoubledRootDepthModel`. Thus the model proposition is discharged
by a theorem; the resulting root-field theorem has no additional premise.

This is an internal derived composition of Library proofs. It supplies no new
transcription of a numbered literature assertion. The root-field statement
and every pair it imports are unchanged. The implementation does not require
constructing an apartment lift or assuming another comparison-field target.

For a supplied lift `L` and lower relative root `a`, the reduction chooses
`Ψ = L.rootFiber a`: the upper relative roots restricting along the actual
torus map to positive integral multiples of the base-changed character `a`.
The split-torus pairing supplies an integral lower cocharacter `ζ` with
positive pairing against `a`. Write `v = (1 : ℝ) ⊗ₜ[ℤ] ζ`; the upper vector
`ν` is `descentCocharacterMap F (UnramifiedClosure F) t.f
P.isMaximalSplitTorus.isSplitSubtorus.1 v`. The reduction's
`exists_rootComparison_of_rootFiberBlockDescent` constructs all seven fields
of `P.IsUnramifiedRootComparison` for these same witnesses:

| Field | Library proof and its role |
| --- | --- |
| `closed` | `L.rootFiber_closed a` proves that the fibre consists of upper roots and is closed under the required positive root combinations. |
| `pos` | `L.rootFiber_pos a v` uses the positive pairing with `a`; evaluation on every fibre root is a positive integral multiple of that pairing. |
| `root_mem` | `L.root_mem_rootFiber a` puts extensions of the lower root group in the upper root-group span of `Ψ`, using the actual torus factorization. |
| `neg_mem` | `L.neg_mem_negativePairingRoots a v` applies opposite-root containment and the negative pairing of the opposite fibre. |
| `levi_mem` | `L.centralizer_mem_pairingLeviSpan_descent_tmul ζ` puts the extended lower centralizer in the pairing Levi for the chosen integral cocharacter. |
| `filtration_mem` | `L.filtration_mem_rootFiber` identifies the lower depth subgroup with the preimage of multiplier-scaled upper depths. At nonnegative depth `r`, every positive multiplier gives depth at least `r`, hence membership in the uniform upper span. |
| `block_mem` | `L.hasRootFiberBlockDescent_of_doubledRootDepthModel` gives the lower ordered block at the same uniform depth `r`, as explained below. It proves a stronger implication that does not need the field's additional lower-root-group membership hypothesis. |

For `block_mem`, `r : ℝ≥0` and membership of an extended lower point in the
uniform upper fibre span are fixed. If `2a` is not a lower relative root,
`L.block_mem_rootFiber_of_not_double` puts the point in the lower filtration
at depth `r`; the identity supplies the second factor. If `2a` is a root,
`RelativeRoot.subgroup_has_smooth_closed_representative` supplies a closed
representative of its actual root functor. The proved
`unramifiedDoubledRootDepthModel` applied at depth `2r` supplies a smooth
integral model with connected special fibre and the exact comparison on
every point over `UnramifiedClosure F`. Unfolding scaled depth gives
`L.IsDoubledRootDepthModelAt y a r q M`. Then
`L.block_mem_rootFiber_of_doubledRootModel` yields the ordered product
`U_(a,y,r) U_(2a,y,r)`.

The latter descent theorem uses the scaled `a` and `2a` factors, their
intersection at scaled doubled-root depth `2r`, and the smooth connected
model to correct the right factor of a Galois-stable decomposition. Exact
filtration preimages then restore both lower factors at depth `r`. Thus the
conclusion preserves the original uniform depth in both factors, including
`r = 0`.

The model theorem used in this composition constructs its model from the
supplied apartment valuation: a descended translation turns depth `2r` into
depth zero at a coefficient-fixed point. Recovered full ambient models and
the recovered split torus give an integral root model, retargeted to the
supplied representative. Its closed integral inclusion, the exact full-model
fixer description and the restricted-root depth-zero theorem give the
comparison in both directions on all unramified points. These are proved
inputs, with no independent coordinate-compatibility assumption.
