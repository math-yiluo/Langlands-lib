# Cyclic subfield norm-one units are single commutators

Let `K : Type uK` be a field, `D : Type uD` a finite-dimensional central
division `K`-algebra, and `L : Type uL` a finite field extension of `K`.
The three universes are independent and arbitrary. No characteristic
restriction appears. Fix an actual algebra map `ι : L →ₐ[K] D`.

For any actual automorphism `σ : L ≃ₐ[K] L`,
`Langlands.CentralDivision.implementingUnit ι σ : Dˣ` chooses the unit
provided by the published field-embedding conjugacy proof, applied to
`ι.comp σ.toAlgHom` and `ι`. Its specification is

`u * ι(a) * u⁻¹ = ι(σ(a))` for every `a : L`,

where `u = implementingUnit ι σ` and the displayed operations are in `D`.
This is `implementingUnit_conj`. Existence of the unit follows from
`exists_unit_conj`; it is not an additional premise. This construction
requires neither a Galois nor a cyclic hypothesis.

Now assume `L/K` is Galois and that `σ` generates its automorphism group,
expressed as `∀ τ, τ ∈ Subgroup.zpowers σ`. For an actual unit `x : Lˣ`
with `Algebra.norm K (x : L) = 1`, the theorem
`exists_commutator_with_implementingUnit_of_norm_eq_one` proves

`∃ v : Dˣ, Units.map ι.toMonoidHom x = ⁅v, implementingUnit ι σ⁆`.

The commutator notation denotes `v * u * v⁻¹ * u⁻¹` in the actual group
`Dˣ`. The proof supplies the constructed unit and its conjugation
identity to the published cyclic Hilbert 90 commutator theorem
`Langlands.CyclicNorm.exists_commutator_of_norm_eq_one`. That theorem
constructs a unit `y : Lˣ` with `x = y / σ(y)` and takes `v` to be its
image under `ι`.

If instead cyclicity is given by `[IsCyclic (L ≃ₐ[K] L)]`,
`exists_commutator_of_cyclic_field_norm_eq_one` chooses a generator by
`IsCyclic.exists_generator` and proves

`∃ v u : Dˣ, Units.map ι.toMonoidHom x = ⁅v, u⁆`.

Neither a generator nor an implementing unit is an argument of this
theorem. Its hypotheses are precisely the field, algebra, finite
dimensionality and centrality conditions above, finite Galois cyclicity,
the specified embedding, the actual unit `x`, and its field norm-one
condition. The theorem
`map_mem_commutator_of_cyclic_field_norm_eq_one` then places this image in
the actual subgroup `commutator Dˣ`, using the generator membership
lemma for the commutator subgroup.

This is an internal deduction from the published field-embedding
conjugacy proof, the explicit cyclic Hilbert 90 construction, and
Mathlib's cyclic-generator and commutator-subgroup APIs. It claims no
new interpretation of an original source.

The norm here is the actual field norm of the supplied finite cyclic
Galois extension. The module does not construct local maximal subfields,
identify this field norm with reduced norm, or move arbitrary
division-algebra reduced-norm-one elements into such a subfield.
Local SK₁ vanishing and `LocalKneserTitsStatement` remain unproved.

Worker 1757 authored this deduction and explanation. Its imported
field-embedding conjugacy proof is by Worker 1791.
