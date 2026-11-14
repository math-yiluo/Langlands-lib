# Extending algebra maps to subalgebras of the generic fibre

Module `Langlands.GroupScheme.IntegralModel.Smoothening.Saturation`. This is a
helper module of the proof of
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`. It contains internal
lemmas only, with no literature counterpart beyond standard commutative algebra.

Throughout, `R` is a domain with fraction field `K`.

## Generic fibre of an algebra

For a commutative `R`-algebra `D`:

- `exists_smul_eq_one_tmul`: every `x ∈ K ⊗[R] D` satisfies `s • x = 1 ⊗ d`
  for some nonzero `s ∈ R` and some `d ∈ D`. This holds because `K ⊗[R] D` is the
  localization of `D` at the nonzero elements of `R`, and is obtained from
  `IsLocalizedModule.surj`.
- `includeRight_injective_of_flat`: if `D` is flat, then `d ↦ 1 ⊗ d` is
  injective (`Algebra.TensorProduct.includeRight_injective`, using injectivity
  of `R → K`). This lemma does not use that `R` is a domain.
- `smul_left_cancel`: multiplication by a nonzero `s ∈ R` is injective on
  `K ⊗[R] D`. It acts as multiplication by the unit `algebraMap R K s`.

## Maps out of a subalgebra `B ⊆ K ⊗[R] A`

Let `A` be a commutative `R`-algebra, `B` an `R`-subalgebra of `K ⊗[R] A` and
`D` a flat commutative `R`-algebra.

- `algHom_ext` (uniqueness): two `R`-algebra maps `g₁ g₂ : B → D` that agree on
  every element `1 ⊗ a` lying in `B` are equal. For `b ∈ B`, write
  `s • b = 1 ⊗ a`. Then `s • g₁ b = s • g₂ b`, and `D` is torsion-free.
- `extend` (existence): let `f : A →ₐ[R] D` satisfy the divisibility hypothesis
  `hf`. Whenever `s ≠ 0` and `s⁻¹ (1 ⊗ a)` lies in `B`, `f a` is divisible by `s`
  in `D`. Then `extend f hf : B →ₐ[R] D` is the restriction of
  `id_K ⊗ f : K ⊗[R] A → K ⊗[R] D`. `map_mem_range` shows that this restriction
  lands in the image of the injective map `D → K ⊗[R] D`. For `b` with
  `s • b = 1 ⊗ a` and `f a = s • d`, the image of `b` is `1 ⊗ d`. The map
  `extend f hf` is this restriction composed with the inverse of
  `AlgEquiv.ofInjective`. `map_mem_range` needs no flatness of `D`.
- `includeRight_extend`: `1 ⊗ extend f hf b = (id_K ⊗ f) b`.
- `extend_apply`: `extend f hf (1 ⊗ a) = f a` when `1 ⊗ a ∈ B`.
