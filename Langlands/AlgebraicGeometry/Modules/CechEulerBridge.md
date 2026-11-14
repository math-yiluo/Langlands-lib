# Čech Euler characteristics of the FLT port and actual Euler characteristics

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.CechEulerBridge` (namespace
`Langlands.AlgebraicGeometry.Modules.CechBridge`) completes `CechHSuccBridge` in degree zero and
for Euler characteristics. It contains only internal helper declarations.

- `homologyZeroEquiv F K`: `H⁰(cechComplex F K) ≃ F.H0 K`, where the FLT `H0` is the kernel of the
  first Čech differential. The incoming differential of an `ℕ`-indexed complex at `0` is zero, so
  the homology is the kernel.
- `h0EquivRelativeCohomology K M`: for `π` separated and `M` quasi-coherent,
  `(ofModules π M).H0 K ≃ H⁰(X, M)` (with the Library's `CechResolution.cechCohomologyIso`).
- `eulerChar_ofModules_eq`: for a nontrivial base ring, `π` separated and `M` quasi-coherent, the
  FLT Čech Euler characteristic `(ofModules π M).eulerChar K` (an alternating sum over
  `p < card K.ι`) equals `∑ᶠ p, (-1)ᵖ dim Hᵖ(X, M)`. The summands agree by the two equivalences.
  Outside `p < card K.ι` the actual cohomology vanishes, because the FLT theorem
  `subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le` makes the corresponding Čech groups
  (or the degree-zero cochains, when the cover is empty) trivial.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
