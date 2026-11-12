# The sharp central depth of an opposite SU3 commutator

This derived coordinate calculation supports the double-root bound in
`CentralizerFiltrationDoubleRootExistenceStatement`. It uses the published
`SU3Root.Parameters` group, its actual upper and opposite matrix embeddings,
`SU3Root.diagonal`, and `SU3Root.Parameters.depthA`. All rings and fields have an
arbitrary universe; no characteristic assumption is used.

`oppositeCommutator p q` is the actual invertible matrix
`lower(q)⁻¹ upper(p) lower(q) upper(p)⁻¹`, with the convention of KP
Definition 7.1.3. Its upper-left entry is
`1 - p.first * bar(q.first) + p.second * q.second`. In any supplied factorization
as `lower(v') diagonal(t) upper(v)`, that entry is the scalar unit `t`.
These assertions are proved by evaluating the published matrices at entry
`(0,0)` and multiplying the finite sums.

If `p.first = 0` or `q.first = 0`, equivalently one parameter belongs to the
literal double-root subgroup `Parameters.central`, the central parameter
satisfies `t - 1 = p.second * q.second`. The exact valuation is therefore
`omega(t - 1) = doubleTop(depthA omega p + depthA omega q)`. The proof uses
valuation multiplicativity and the normalization `depthA p = omega(p.second)/2`,
with separate finite and infinite value cases. For a finite sum `r`, this
specializes to `omega(t - 1) = 2*r`; no sign assumption on either depth or their
sum is needed.

The provenance is derived from the concrete `SU3` computation in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), proof of
Proposition 7.1.1, printed pp.239–240 / PDF pp.270–271, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The sign in the first-coordinate
term reflects the existing `oppositeEmbedding` convention. The authors'
*Corrections and additions* (1 November 2024), registered as
`kaletha-prasad-2024-corrections`, Chapter 7, PDF pp.33–35, do not change that
calculation.

This module assumes the displayed factorization when extracting its central
parameter. It does not construct a filtration of tori, identify arbitrary
relative-root groups with these matrices, or descend a filtration from an
unramified extension. Those remain obligations of the full existence proof.
