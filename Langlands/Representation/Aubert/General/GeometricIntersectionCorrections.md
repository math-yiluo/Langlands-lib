# Both original Haar corrections on the literal common Levi

This internal construction by Worker 184 pulls the two existing
`Geometric.General.haarCorrectionCharacter` characters to the literal target
common Levi. Its provenance is the published original Haar correction
construction, the subgroup equality transports in
`GeometricIntersectionTransport`, and the inverse conjugation implemented in
`GeometricCoefficientAction`.

For arbitrary subgroups `MI`, `MJ` of a group `A : Type uG` and any `n : A`, the
common Levi is `(geometricTargetIntersection MI MJ n).subgroupOf MI`.
`geometricTargetCorrectionTransport` maps it to the original
`Geometric.General.intersectionIn MI MJ n⁻¹` by equality, retaining the ambient
point. `geometricSourceCorrectionTransport` sends it to
`n⁻¹ x n` in `Geometric.General.intersectionIn MJ MI n`.
`geometricSourceCorrectionTransport_eq` identifies it with the inverse of
`Geometric.General.intersectionEquiv MJ MI n`, after the target equality
transport. The proof compares the ambient values of the two nested subtypes.
The target transport is continuous for any topology on `A`; continuity of the
source transport uses the topological-group structure and continuity of
multiplication.

In the locally compact topological-group setting, the source correction uses
the original data `(MJ, MI, UJ, PI, n)`. Its original radical is `UJ`; its original
correction subgroup consists of `u ∈ UJ` such that `n u n⁻¹ ∈ PI`.
It requires `UJ` and `PI` closed, `MJ ≤ normalizer UJ` and
`MI ≤ normalizer PI`. The target correction uses
`(MI, MJ, UI, PJ, n⁻¹)`. Its original radical is `UI`; its original correction
subgroup consists of `u ∈ UI` such that `n⁻¹ u n ∈ PJ`.
It requires `UI` and `PJ` closed, `MI ≤ normalizer UI` and
`MJ ≤ normalizer PJ`. Each construction uses only the hypotheses relevant
to its own side.

The four `geometric*Correction*Modulus` definitions compose the original
positive characters with the corresponding transport.
`geometricSourceCorrectionCharacter` and `geometricTargetCorrectionCharacter`
compose the original complex correction characters with those same maps.
The two `*Character_eq` theorems are definitional equalities: each character
is the complex positive half of its transported original radical modulus
multiplied by the inverse half of its transported original correction-subgroup
modulus. These are the canonical positive real square roots embedded in the
complex units. The two `*Character_sq` theorems specialize
`Geometric.General.haarCorrectionCharacter_sq` at the transported point and
retain the radical-over-correction ratio.

If `A` is nonarchimedean, the `isOpen_ker_geometric*CorrectionCharacter`
theorems use continuity of the transports to pull back
`Geometric.General.isOpen_ker_haarCorrectionCharacter`. This constructs both
`Induction.SmoothCharacter` objects and both scalar twist functors on the
identical literal common Levi. The representation carrier universe `uV` is
independent of `uG`. The `*Twist_action` lemmas expose the exact scalar action
of each original correction.

The proof bodies use the published subgroup equality and conjugation maps,
the original correction square and smoothness theorems, and scalar twisting.
They use no geometric-lemma comparison, adjointness, cuspidal support,
character independence, or classification theorem. The imported
`GeometricCoefficientAction` module and its transitive closure contain further
coefficient constructions; this module does not invoke their rational-point
coefficient equivalences. No identity between the two corrections, balance
between distinct-radical moduli, compact/full induction comparison, orbit
filtration or K0 expansion is established here.
