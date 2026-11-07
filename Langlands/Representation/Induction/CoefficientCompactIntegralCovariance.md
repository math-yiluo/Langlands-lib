# Native compact integral: naturality and automorphism covariance

This internal extension of `CoefficientCompactCoinvariants` retains the original
compact functions and native coefficient quotients over a commutative complex
algebra `R`. The coefficient ring, group and two inducing carriers have independent
universes. It derives its formulas from the published complex integral and its
automorphism covariance.

`complexIntertwiningMap` restricts each actual native inducing intertwiner to
complex scalars. The full-quotient and compact-function comparisons commute with
this map because they preserve original vector classes and original function
values. Applying the complex integral's naturality therefore proves
`compactCoinvariantIntegral_natural` over `R`. Quotient surjectivity then gives
`compactCoinvariantDesc_natural_apply` and the equality of native linear maps
`compactCoinvariantDesc_natural`. This part only needs a Borel quotient measure
finite on compact sets, and descent additionally needs all quotient right
translations to preserve that measure.

For a continuous group automorphism `α` preserving the subgroup `H`,
`automorphismCoinvariantsEquiv` is an `R`-linear equivalence from the full
coinvariants of the pulled-back inducing action to the original full
coinvariants. Both directions send the class of a vector to the class of the
same vector. The quotient lifts exist because the restricting automorphism
runs through every element of `H`. The construction is natural in all native
inducing intertwiners. It commutes with the complex scalar-restriction comparison;
compact precomposition also commutes with scalar restriction on the original
functions.

`compactCoinvariantIntegral_automorphism` assumes a Hausdorff locally compact
ambient group, a closed subgroup, Borel measurable structures, supplied regular
ambient and subgroup Haar measures, a right-invariant subgroup Haar measure,
and a supplied compatible quotient measure finite on compact sets. The subgroup
is locally compact. These are the retained hypotheses of the complex covariance
theorem. Forward precomposition `f ↦ f ∘ α`, followed by the native
identity-on-classes quotient transport, scales the original native integral by
the complex scalar `δH / δG`, where each `δ` is the actual
`MeasureTheory.mulEquivHaarChar` of the automorphism or its restriction. The
proof transports the published complex identity through the actual quotient
comparison. No smoothness or bijectivity assumption is needed for this formula.

This unit provides naturality and automorphism covariance of the native full
compact-induction integral. Partial radical coinvariants with their Levi action,
the split-stage orbit comparison, cancellation of normalization characters,
actual rational orbit geometry, compatible-measure existence and the final
universal-family fixed-module finiteness remain separate obligations.
