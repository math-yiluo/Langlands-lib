# An admissible carrier for the place actions at a real place

Module `Langlands.Automorphic.PlaceComponentCarrier`. Worker 174 wrote it as a step towards G1
(Task 5992). Provenance: internal.

Let `S` be an operator realization of `GL_n` over a number field `F` and `v` a real place.
`ArchimedeanCompactFactors F n = ∏_{w real} O(n) × ∏_{w complex} U(n)`. Its Library map
`toStandardCompact` is injective and surjective onto the standard compact `K_∞`.

## Splitting the compact at `v`

- `awayReal v`: the homomorphism of compact factors replacing the component at `v` by `1`.
- `awayReal_fst_self`: the result has trivial component at `v`.
- `eq_realPlaceFactor_mul_awayReal`: `p = (p_v at v) · awayReal v p`.
- `commute_realPlaceFactor`: factors trivial at `v` commute with factors supported at `v`.
- `factorEquiv`: the inverse isomorphism `K_∞ ≃* ArchimedeanCompactFactors`, and
  `toStandardCompact_factorEquiv`.
- `OperatorRealization.compact_comm_realPlaceCompact` and `compact_comm_realPlaceLie`:
  compact translations by factors trivial at `v` commute with the place actions at `v`. For
  the Lie action, the Library's full compact covariance applies with conjugation by `1`.
- `OperatorRealization.compact_eq_realPlace_mul`:
  `κ(k) = κ_v(k_v) ∘ κ(awayReal v k)`.

## The carrier

`OperatorRealization.realCarrier v L R`, for a subgroup `L` of the finite adelic group and a
representation `R` of the compact factors on `ℂ^m`, is the space of linear maps
`φ : ℂ^m → S` such that:

- every value is `L`-fixed;
- `φ(R q x) = κ(q) φ(x)` for all factors `q` trivial at `v`.

It is a definition for this proof (`mem_realCarrier`).

- `isStable_realCarrier`: post-composition with the place actions at `v` preserves the
  carrier. They commute with finite translations (Library lemmas) and with compact
  translations away from `v`.
- `matrixRep τ` (a matrix representation acting on column vectors), `conjRep ε ρ` (transport
  of a representation along a linear equivalence) and `realCarrierRep v τ R`. The last is
  the representation `k ↦ τ(k_v) ⊗ R(awayReal v k)` of `K_∞` on `ℂ^d ⊗ ℂ^m` (Mathlib's
  `Representation.tprod`).
- `lift_mem_jointMultiplicity`: let `Φ` be a `τ`-intertwiner into the carrier. Then the
  curried map `TensorProduct.lift Φ` on `ℂ^d ⊗ ℂ^m` has `L`-fixed values and intertwines
  `realCarrierRep v τ R` with the compact action of `S`. On a pure tensor `a ⊗ b`, its value
  `Φ(τ(k_v) a)(R(k^v) b)` becomes `κ_v(k_v) κ(k^v) Φ(a)(b) = κ(k) Φ(a)(b)`.
- `isAdmissible_realCarrier`: if `S` is jointly admissible and `L` is open, the carrier is
  admissible for `O(n)`. `Φ ↦ TensorProduct.lift Φ ∘ ε⁻¹` (`ε` a basis isomorphism with
  `Fin N → ℂ`) is linear and injective into the joint multiplicity space of
  `conjRep ε (realCarrierRep v τ R)`, which is finite-dimensional.
