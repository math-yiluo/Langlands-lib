# Topology on actual adelic group-scheme points

Author: Worker 94.

Let `F` be any number field and `G` the actual group scheme over `Spec F`.
Assume that its underlying scheme is affine. The three adelic point groups
retain their existing scheme-morphism carriers and group laws, with the
global-function evaluation topology. The imported
`affinePointsIsTopologicalGroup` supplies their topological group structure
from the topological ring structure of each coefficient algebra.

This unit supplies Hausdorff instances for full, finite and archimedean
adelic points. For a structure morphism locally of finite type it also supplies
local compactness. The finite coefficient ring has its actual restricted-product
topology; its local compactness is the published
`finiteAdeles_locallyCompactSpace`. The infinite coefficient ring is the finite
product of archimedean completions. The full ring is their product and uses the
published `adeles_locallyCompactSpace`. The finite-coordinate result
`affinePointsLocallyCompactSpace` transfers these coefficient facts to actual
group-scheme points. No reductivity, splitting, smoothness or choice of
faithful representation is needed for these assertions.

For the published `GeneralLinear.groupScheme (Fin n) F`, the definitions
`adelicHomeomorph`, `finiteHomeomorph` and `infiniteHomeomorph` specialize the
proved `GeneralLinear.affinePointsHomeomorph` to these actual coefficient
rings. Their underlying multiplicative equivalences are definitionally the
previous `adelicEquiv`, `finiteEquiv` and `infiniteEquiv`. The targets are the
existing matrix unit groups with their units topologies, not replacement
matrix models. `adelicHomeomorph_rational` retains the previous compatibility
with the actual diagonal principal matrix map. All natural-number ranks,
including zero, are included.

This is an internal specialization of the affine point constructions in
Getz–Hahn, *An introduction to automorphic representations* (2024), §2.2,
Theorem 2.2.1 and Proposition 2.2.2, printed pp.51–54, using the actual
number-field coefficient rings of §2.3, printed pp.55–57. Registered source
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The local-compactness argument is exactly the previously proved
finite-coordinate argument and coefficient local compactness.

This unit does not identify general adelic points with a restricted product
of local group points. It makes no second-countability assertion, no
discreteness or closedness assertion about rational points, and no quotient,
measure, finite-volume or reduction-theory assertion.
