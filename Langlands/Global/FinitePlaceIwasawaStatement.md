# Actual finite-place parabolic Iwasawa existence

Authors: Worker 399 and Worker 1430.

`Langlands.Global.FinitePlaceGroupPoints.ParabolicIwasawaStatement` is an
unproved proposition definition naming the finite-place existence input of
actual adelic Iwasawa assembly. It quantifies over every number field
`F : Type u`, actual group scheme `G` over `Spec F` satisfying the existing
`IsConnectedReductive G`, actual group-scheme morphism `p : P ⟶ G`
satisfying the existing `IsParabolicSubgroup p`, and finite place `v`.
It concludes existence of a subgroup `K` of
`FinitePlaceGroupPoints F G v` satisfying the published
`CoordinateCompactPatching.IsLocalIwasawaCompact` predicate.

Unfolding that predicate gives precisely:

1. `IsCompact (K : Set (FinitePlaceGroupPoints F G v))`.
2. For every subgroup `L` of the same group, if `L` is compact and
   contains `K`, then `L = K`.
3. The literal pointwise set equality
   `Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
   (K : Set _) = Set.univ`.

The parabolic image is the left factor and the compact subgroup is the
right factor. Maximality ranges over all compact subgroups. The subgroup
is chosen after the field, group, parabolic inclusion and place; this
statement requires no simultaneous choice for different parabolics.
The carrier, imported from `AdelicGroupLocalPoints`, abbreviates
`G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))`. Its topology
is the existing topology induced by evaluation of all global regular
functions in the actual finite completion. The map is the existing
completion-valued point homomorphism induced by postcomposition with `p`.

The proposition retains universe `u` and the original reductive and
parabolic predicates. It adds no splitness, isotropy, chosen model,
special point, compact subgroup, decomposition or topology-comparison
premise. Non-split and anisotropic groups and the improper parabolic
remain in scope.

The provenance is derived: this consumer interface names exactly the
finite-completion premise in the companion module
`AdelicIwasawaReduction`. Its source motivation is the finite-local
consequence of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Appendix B, Theorem B.1.1 and (B.1), printed p.541, and
Proposition B.4.2 and Theorem B.4.3, printed p.548. Registered source:
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
These passages and the complete October 2026 author errata were read;
the errata contains no Appendix B correction.

The source obtains a stronger simultaneous conclusion for standard
parabolic pairs from a special-point stabilizer in the norm-one group,
its maximal compactness, parahoric containment and the local Iwasawa
product. This proposition asks only for the displayed existence
conclusion. A proof through that route must establish the corrected
building data and special-point existence, the actual stabilizer and
parahoric comparisons, the product for every actual rational parabolic,
and the topology and base-change comparisons needed on the actual
completion-point carrier. No supplementary special-compact statement or
conditional local-product interface is asserted to prove this target.
The existing nonarchimedean program retains those proof obligations.

This module supplies no existence proof. The companion reduction uses
this proposition, the archimedean existence proposition and the integral
family existence proposition as three explicit premises. Neither this
statement nor that conditional theorem proves the unconditional adelic
target.
