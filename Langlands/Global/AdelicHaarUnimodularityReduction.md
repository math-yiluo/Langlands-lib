# Reduction of actual adelic Haar unimodularity

This internal unit assembles the existing analytic, subgroup, and
algebraic reductions for the exact
`AdelicGroupPoints.AdelicHaarUnimodularityStatement`.
Every universal assertion retains the same arbitrary universe `u`.
The original number fields, group schemes, adelic point topologies,
norm-one character kernels, and fixed Haar measures are used throughout.

`AdelicHaarUnimodularityReductionStatement` is a proposition definition
stating that the existing universal local analytic formula and universal
reductive determinant triviality imply that exact conjunction.
`adelicHaarUnimodularityReduction` proves this conditional proposition by
the reductions below.

`normOneHaarRightInvariantStatement_of_modularComparison` assumes the
existing universal adelic modular-character comparison. For every smooth
connected affine group in the target, it specializes that comparison to
the actual rational adjoint determinant character. The existing
`normOneHaarRightInvariant_of_characterNorm` then proves right invariance
of the subgroup's own fixed Haar measure. That helper identifies the
intrinsic subgroup modular character with the ambient restriction,
uses membership in every character-norm kernel, and applies Haar scaling.
The group in this assertion need not be reductive.

`connectedReductiveHaarRightInvariantStatement_of_modularComparison`
also assumes the existing universal reductive adjoint-determinant
triviality statement. For a connected reductive group, its existing
predicate supplies smoothness and connectedness for the analytic
comparison. Determinant triviality makes the character norm one, so
the existing Haar-scaling helper proves right invariance of the full
actual adelic Haar measure.

`adelicHaarUnimodularityStatement_of_modularComparison` pairs these
conclusions. Its conclusion is exactly the existing conjunction, with
the analytic comparison and algebraic determinant statement as explicit
premises.

`normOneHaarRightInvariantStatement_of_local` and
`adelicHaarUnimodularityStatement_of_local` replace the adelic analytic
premise by the existing all-place local analytic statement. They apply
the proved local-to-adelic assembly, which uses actual local insertions,
closed-normal modular restriction, normalized local character norms,
continuity, and convergence of finite local truncations. The normalized
complex-place factor remains squared.

Finally,
`adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct`
obtains the determinant premise from the existing conditional algebraic
reduction. It assumes the central-times-derived product statement and
uses central triviality and annihilation of the derived subgroup.

The provenance is internal: the reductions compose the named existing
Library interfaces. They identify the remaining proof obligations of the
Getz–Hahn §3.6 argument without adding a measure or choosing another point
group. This module does not prove either the local analytic formula or
the reductive structural statement. Its conditional conclusions do not
discharge the unconditional Haar-unimodularity target.
