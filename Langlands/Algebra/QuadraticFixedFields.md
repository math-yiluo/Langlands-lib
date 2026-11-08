# Index-two Galois subgroups and separable quadratic intermediate extensions

This module is field theory over Mathlib. Its only Library import is
`Langlands.GroupScheme.Examples.SU3RootParametersQuadratic`, for the conjugation
`SU3Root.conjugation K₀ K` of a separable quadratic extension `K / K₀`, and its uniqueness
lemma `SU3Root.conjugation_unique`.

Let `L / k` be a finite Galois extension and `K₀ ⊆ K` intermediate fields. The module shows
three things. The degree `[K : K₀]` is the relative index of the fixing subgroup of `K` in the
fixing subgroup of `K₀`. When this index is `2`, `K / K₀` is a separable quadratic extension.
And every Galois element that fixes `K₀` but not `K` maps `K` into itself, where it acts as
the conjugation `SU3Root.conjugation K₀ K`.

The intended use is the multipliable relative roots of a quasi-split group. There `K` is the
field of an absolute root `β`, `K₀` is the field of the root `β + β'` for its orbit partner
`β'`, and the index-two statement comes from the module
`Langlands.GroupScheme.Reductive.RootDatumOrbitPartners`. This module makes no reference to
roots.

Provenance: internal. These are standard consequences of the fundamental theorem of Galois
theory. The proofs use only the Mathlib facts listed below.

All declarations live in namespace `Langlands.Algebra.QuadraticFixedFields`. The variables
are fields `k L : Type u` with `[Algebra k L]` and intermediate fields
`K₀ K : IntermediateField k L`. Mathlib has no algebra instance between nested intermediate
fields, so the module assumes `[Algebra K₀ K] [IsScalarTower K₀ K L]` and derives `K₀ ≤ K`
from them. Section `Galois` also assumes `[FiniteDimensional k L] [IsGalois k L]`. Lemmas that
do not need some of these assumptions drop them with `omit`.

## Nested intermediate fields

- `nestedAlgebra K₀ K h : Algebra K₀ K` for `h : K₀ ≤ K`: the algebra given by
  `IntermediateField.inclusion h`. It is a reducible `def`, not an instance.
  `nestedAlgebra_isScalarTower` shows that it gives a scalar tower `K₀ → K → L`. A caller
  holding `h : K₀ ≤ K` can use these two to supply the assumptions of the module.
- `coe_algebraMap`: under the scalar-tower assumption, `((algebraMap K₀ K x : K) : L) = x`.
  So every such algebra structure is the inclusion.
- `le_of_isScalarTower : K₀ ≤ K`.
- `isScalarTower_base : IsScalarTower k K₀ K`.

## Degrees and relative indices

- `nat_card_eq_relIndex_mul`: for subgroups `H ≤ H'` of the finite group `L ≃ₐ[k] L`,
  `Nat.card H' = H.relIndex H' * Nat.card H`. Proof: multiply both sides by `H'.index`. Then
  use `Subgroup.card_mul_index` on each side and `Subgroup.relIndex_mul_index`. The index of
  `H'` is nonzero because the group is finite.
- `fixingSubgroup_le`: `K.fixingSubgroup ≤ K₀.fixingSubgroup`.
- `finrank_eq_relIndex`:
  `finrank K₀ K = K.fixingSubgroup.relIndex K₀.fixingSubgroup`.
  Proof. The tower law gives `finrank K₀ K * finrank K L = finrank K₀ L`. Mathlib's
  `IsGalois.card_fixingSubgroup_eq_finrank` rewrites `finrank K L` and `finrank K₀ L` as
  the orders of the fixing subgroups of `K` and `K₀`. By `nat_card_eq_relIndex_mul`, the
  order for `K₀` is the relative index times the order for `K`. Cancel the nonzero order of
  the fixing subgroup of `K`.
- `isQuadraticExtension`: if the relative index is `2`, then
  `Algebra.IsQuadraticExtension K₀ K`.
- `isSeparable`: `Algebra.IsSeparable K₀ K`, from separability of `L / k` by
  `Algebra.isSeparable_tower_bot_of_isSeparable`.
- `relIndex_eq_two`: conversely, under `[Algebra.IsQuadraticExtension K₀ K]` the relative
  index is `2`.

## Conjugation

Fix `h2`, the hypothesis that the relative index is `2`, and an element
`s ∈ K₀.fixingSubgroup`.

- `conj_mem_fixingSubgroup`: for `g ∈ K.fixingSubgroup`, `s * g * s⁻¹ ∈ K.fixingSubgroup`.
  Proof: inside `K₀.fixingSubgroup`, the fixing subgroup of `K` has index `2`, so it is normal
  (`Subgroup.normal_of_index_eq_two`).
- `apply_mem`: for `x ∈ K`, `s x ∈ K`. Proof: `K` is the fixed field of its fixing subgroup
  (`IsGalois.fixedField_fixingSubgroup`). For `g` in that subgroup,
  `s⁻¹ * g * s` also fixes `x` by `conj_mem_fixingSubgroup`, so `g (s x) = s x`.
- `restrict K₀ K h2 s hs : K ≃ₐ[K₀] K`: the restriction of `s` to `K`. Its inverse is the
  restriction of `s.symm`, and it fixes `K₀` because `s` does. `coe_restrict` says that
  `restrict K₀ K h2 s hs x` has underlying element `s x` (by `rfl`).
- `restrict_ne_one`: if `s ∉ K.fixingSubgroup`, the restriction is not the identity.
- `conjugation_apply`: assume `[Algebra.IsQuadraticExtension K₀ K]` and
  `[Algebra.IsSeparable K₀ K]`. If `s ∈ K₀.fixingSubgroup` and `s ∉ K.fixingSubgroup`, then
  for every `x : K`,
  `(SU3Root.conjugation K₀ K x : L) = s x`.
  Proof: by `relIndex_eq_two` the restriction is defined. It is not the identity, so it
  equals `SU3Root.conjugation K₀ K` by `SU3Root.conjugation_unique`.
- `exists_mem_not_mem`: if the relative index is `2`, some `s ∈ K₀.fixingSubgroup` is not in
  `K.fixingSubgroup`. Otherwise the relative index would be `1` (`Subgroup.relIndex_eq_one`).
  This lemma needs neither finiteness nor the scalar-tower assumption.
- `conjugation_eq_self_iff`: under the quadratic and separable assumptions,
  `SU3Root.conjugation K₀ K x = x ↔ (x : L) ∈ K₀`.
  Proof. Suppose the conjugation fixes `x`. Then `x` is fixed by every `g` fixing `K₀`. For
  `g` fixing `K` this is clear. For the other `g` it is `conjugation_apply`. Hence `x` lies in
  the fixed field of `K₀.fixingSubgroup`, which is `K₀`. Conversely, choose `s` by
  `exists_mem_not_mem` and use `conjugation_apply`: `s` fixes elements of `K₀`.

## Scope

The module does not identify `K` or `K₀` with root fields, and it does not construct the
index-two subgroups. Those inputs come from the callers.
