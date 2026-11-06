# An actual compatible tower of pointed Picard source quotients

This internal construction iterates the actual pointed source successor and
constructs a Noetherian local quotient of the fixed source with compatible
surjective maps to every stage. The quotient is separated by those maps.
No identification with an inverse limit, adic comparison, completeness or
formal versality is asserted in this module.

Fix a commutative ring `k`, a field `K` with its given `k`-algebra structure,
a commutative Noetherian local `k`-algebra `R` with a specified surjective
augmentation `ε : R →ₐ[k] K`, an actual flat proper scheme morphism
`f : X → Spec k`, and an actual line bundle `M` on the residue-fibre relative
scheme. Supply an actual `ArtinianPicardSourceStep.Stage ε f M` called `s₀`.
It consists of an augmented Artinian test, a surjective presentation from `R`
with the exact augmentation equation, and an actual pointed deformation of
`M`. All objects have arbitrary common universe `u`. No coefficient-field
section or new `K`-algebra structure on the tests is chosen.

`stage` uses natural-number recursion, with initial value `s₀` and successor
`Stage.next`. The equations `stage_zero` and `stage_succ` are reflexive.
Thus each step uses the actual source extension quotient by the smallest
subspace that allows a pointed lift, as constructed in the imported module.
The abbreviations `test`, `cover` and `family` retain the actual test,
surjective fixed-source presentation and actual pointed deformation at each
stage. `cover_surjective` and `augmentation_cover` are their original fields.

`step n` is the actual elementary reduction from stage `n+1` to stage `n`.
`step_elementary` reuses the successor's elementary theorem, and `step_cover`
retains the exact equality between the two presentations after reduction.
`transition n` is the successor's actual pointed restriction isomorphism at
`stage n`; `stage_succ` identifies its source stage with `stage (n+1)`.
Its type is inferred directly from that existing isomorphism, so it retains
the full pointed bundle and prescribed residue data without re-elaborating
its large dependent category type.

Write `J_n` for `equations n`, the actual kernel of the stage-n presentation,
and `m` for the maximal ideal of `R`. The successor bounds give

```text
m * J_n ≤ J_(n+1) ≤ J_n.
```

`equations_antitone` extends the second bound to every ordered pair of
indices. Induction using the first bound proves
`maximalIdeal_pow_mul_equations_le`, namely `m^n * J_0 ≤ J_n`.
For any initial power bound `m^a ≤ J_0`, `maximalIdeal_pow_le` proves
`m^(n+a) ≤ J_n`, by multiplication of ideals and the preceding theorem.
These are containments of actual ideals in the one original source ring.

`limitingEquations` is the intersection `J_∞ = ⋂ n, J_n`.
`limitingEquations_le` gives its inclusion in every stage ideal, and
`limitingEquations_le_augmentation` uses stage zero's augmentation equation
to place it in the kernel of `ε`.
`limitRing` is the actual quotient ring `R/J_∞`.
`limitAugmentation` is the original augmentation descended through this
quotient, with surjectivity inherited from `ε`.
The augmentation makes the quotient nontrivial. The usual surjective
quotient theorems give its local and Noetherian ring instances.

For every stage, `projection n` descends the original source cover through
`J_∞ ≤ J_n`, and `projection_surjective` follows from the surjectivity of
that cover. `projection_step` proves compatibility with the actual
consecutive test arrow, by extensionality through the quotient map and
`step_cover`. Similarly `augmentation_projection` proves that every
projection retains the original descended augmentation.

`ker_projection` identifies each projection kernel with the actual image
of `J_n` in `R/J_∞`, by the quotient-lift kernel formula.
`iInf_ker_projection` proves that the intersection of all these kernels is
zero. Represent an element of the quotient by `a : R`. Its image being zero
in every stage means `a ∈ J_n` for every `n`, hence `a ∈ J_∞`; its original
quotient class is therefore zero. This proves joint separation of the
projections. It does not prove existence of a quotient element realizing
an arbitrary compatible tuple of stage elements.

The provenance is internal: recursion iterates the existing actual
successor, and the ring results use actual kernels, ideal operations and
quotient maps. Comparison of the stage ideals with powers of the limiting
maximal ideal, completeness and an inverse-limit identification, conversion
to an actual formal line-bundle system, formal versality, effectivity,
algebraization and the exact field Picard-stack atlas remain separate
obligations.
