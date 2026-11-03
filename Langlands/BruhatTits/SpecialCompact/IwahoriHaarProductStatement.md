# Haar characters from a simultaneous Iwahori basis

This internal statement concerns an arbitrary locally compact topological group
`G`, in any universe, equipped with its Borel measurable structure. Let `M`,
`U`, and `V` be closed subgroups, let `P` contain `M` and `U`, and assume
`V ∩ P = {1}`.

The hypotheses supply one cofinal identity-neighborhood basis `B` of compact
open subgroups, all contained and normal in the same subgroup `K0`. Every
member has the unique ordered factorization by its literal intersections
with `V`, `M`, and `U`, as defined by
`HasIwahoriIntersectionDecomposition`.

Let `α` be a continuous group automorphism of `G`, and let `αM`, `αU`, and
`αV` be continuous automorphisms of the three subgroups. Their compatibility
with inclusion is explicit: applying `α` to a subgroup element is the same
as including the corresponding restricted automorphism's value. Then

`mulEquivHaarChar α = mulEquivHaarChar αV * mulEquivHaarChar αM * mulEquivHaarChar αU`.

The subgroup topologies and measurable structures are inherited. Closedness
supplies their local compactness internally. The Haar characters use Mathlib's
image-measure scaling convention.

The intended internal derivation chooses a basis member `K`, a smaller member
`J` with both `J` and `α(J)` contained in `K`, and a further common basis
member `H` contained in `J ∩ α(J)`. Normality in `K0` gives normality of
`H` in `K`. Compactness makes its index finite. The compatible factorization
transports from `J` to `α(J)`. The relative-index product for both subgroups,
combined with the compact-open Haar-index formula in `G` and in each closed
factor, gives the claimed identity by cancellation of a positive finite
index.

This is a general conditional analytic target, not a construction of the
basis or of actual reductive-group subgroups. It does not assert opposite
Haar reciprocity, torus centralization, a Cartan covering, or unimodularity.
Those remain separate obligations in the rational-parabolic application.
