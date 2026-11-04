# Open units in actual adelic-level local factors

The theorem `adelicLocalFactorUnits` proves exactly
`Langlands.Global.AdelicLocalFactorUnitsStatement` at an arbitrary common
universe. It uses the original completion and valuation-subring topologies
supplied by `AdelicLevelModelPoints`, preserving every finite S and all infinite
number-field factors. No assumption on finite constants, separability,
perfectness or function-field finiteness is added.

The helper `isOpenUnits_openSubring` treats an open subring A of a commutative
ring B satisfying `IsOpenUnits B`. The inclusion A → B is a topological
embedding; Mathlib's `IsEmbedding.units_map` shows that the induced map Aˣ → Bˣ
is an embedding for the existing value-and-inverse unit topologies. Its image
is exactly `A.toSubmonoid.units`: an ambient unit is in the image precisely
when its value and inverse both belong to A. The proof constructs the unit in
A directly in the reverse direction. This image is open by
`Submonoid.isOpen_units`. Composing the resulting open embedding with the
ambient unit inclusion Bˣ → B and cancelling the open inclusion A → B proves
that Aˣ → A is an open embedding. No localness or continuity of ring operations
is needed for this helper.

The entry theorem splits the actual factor index. Completed fields have
`IsOpenUnits` through Mathlib's field instance (continuous inversion away from
zero and the T1 property). Completed valuation subrings are open by
`Valued.isOpen_valuationSubring`, so the helper supplies their result with the
existing subspace topology. This yields both conjuncts of the exact target.
The result supplies the local prerequisite for subsequent arithmetic
scheme-point functoriality; no adelic transition, descent or global-colimit
property is claimed here.
