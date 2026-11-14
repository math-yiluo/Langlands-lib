# An admissible carrier for the place actions at a complex place

Module `Langlands.Automorphic.PlaceComponentCarrierComplex`. Worker 174 wrote it as a step towards
G1 (Task 5992). Provenance: internal. It is the complex-place analogue of
`Langlands.Automorphic.PlaceComponentCarrier`, whose `factorEquiv`, `matrixRep` and `conjRep` it
reuses. Here `v` is a complex place, `K_v = U(n)`, and the factor at `v` is the component
`p.2 v`.

- `awayComplex v`, `awayComplex_snd_self`, `eq_complexPlaceFactor_mul_awayComplex` and
  `commute_complexPlaceFactor`: splitting the compact factors at `v`.
- `OperatorRealization.compact_comm_complexPlaceCompact`, `compact_comm_complexPlaceLie` and
  `compact_eq_complexPlace_mul`: compact translations away from `v` commute with the place
  actions at `v`, and `κ(k) = κ_v(k_v) ∘ κ(awayComplex v k)`.
- `OperatorRealization.complexCarrier v L R`: linear maps `ℂ^m → S` with `L`-fixed values
  intertwining `R` with the compact action on factors trivial at `v`.
  `isStable_complexCarrier`: it is stable under post-composition with the place actions at
  `v`.
- `complexCarrierRep v τ R`: the representation `k ↦ τ(k_v) ⊗ R(awayComplex v k)` of `K_∞`.
- `lift_mem_jointMultiplicity_complex`: the curried form of an intertwiner into the carrier
  lies in the joint multiplicity space.
- `isAdmissible_complexCarrier`: the carrier is admissible for `U(n)` when `S` is jointly
  admissible.

The proofs are those of the real case with the second component of the compact factors.
