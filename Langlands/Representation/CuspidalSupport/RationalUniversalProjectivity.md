# Projectivity of the actual norm-kernel compact induction

This internal construction proves ambient projectivity of
`rationalNormKernelCompactInduction G π`, conditional on compact smooth-dual
coefficients of the **entire** restriction of `π` to
`rationalCommonNormKernel G`. It also constructs lifts inside the actual inertia
block when actual block membership is supplied. The field and original carrier
universes are independent. No irreducibility, admissibility or finite-length
premise enters this conditional result.

The generic theorem `Induction.projective_compactInduced_of_compactCoefficients`
first raises the inducing carrier with the published `SmoothRep.universeLift`.
The actual cross-universe representation equivalence preserves compact
smooth-dual coefficients. The compact-coefficient projectivity theorem applies
to this raised object. Open-subgroup compact induction preserves projectivity
by its published adjunction to restriction. Postcomposition with the actual
carrier equivalence gives an equivalence of the two compact inductions; their
carriers now lie in the same function-carrier universe. Projectivity transports
back along the resulting categorical isomorphism. Local compactness of the
open subgroup follows from ambient local compactness.

`rationalNormKernelCompactInduction_projective` applies that theorem to the
literal complete norm-kernel restriction. The canonical rational-point topology
is Hausdorff, locally compact and totally disconnected, and the actual norm
kernel is open, by the published local-field and point-topology results.
`rationalNormKernelCompactInduction_block_projective` transfers ambient
projectivity into the full rational inertia block using the existing block
lifting construction. `rationalNormKernelBlockProjectiveLift` selects its
categorical lift, and the accompanying composition theorem proves that the
lift followed by the given epimorphism equals the original morphism.

The provenance is internal: the construction combines existing carrier lifts,
coefficient invariance, compact-coefficient projectivity, the open-subgroup
adjunction, compact-induction equivalence and full-block lifting. It is a
conditional supporting construction for Renard VI.4.1, not a proof of
`RationalUniversalSmallProgeneratorStatement`. Deriving compactness of the
restriction from the target's exact cuspidality assumptions, proving actual
block membership, and proving faithful Hom and smallness remain separate
obligations. The published target is unchanged.
