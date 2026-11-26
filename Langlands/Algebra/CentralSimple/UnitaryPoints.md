# Unitary and special unitary points of a central simple algebra with involution

Module: `Langlands.Algebra.CentralSimple.UnitaryPoints`.

Let `F` and `E` be fields with `Algebra F E`, and let `B` be a ring with
`Algebra E B`, `Algebra F B` and `IsScalarTower F E B`. An `F`-linear involution
of `B` is a `Langlands.GroupScheme.Quaternionic.FirstKindInvolution F B`: an
`F`-linear map `τ` with `τ 1 = 1`, `τ (x * y) = τ y * τ x` and `τ (τ x) = x`.
For a commutative `F`-algebra `R`, `τ.baseChange R` is `id_R ⊗ τ` on `R ⊗[F] B`.
All types are in one universe `u`. The module works in the namespace
`Langlands.CentralSimple.UnitaryPoints`.

## Declarations

- `tensorEquiv F E B R : R ⊗[F] B ≃ₐ[F] (E ⊗[F] R) ⊗[E] B` is the canonical
  identification, `r ⊗ b ↦ (1 ⊗ r) ⊗ b` (`tensorEquiv_tmul`, by `rfl`). It is the
  composite of commutativity, the right unit `B ≃ B ⊗[E] E` and associativity of
  tensor products. `tensorEquiv_naturality` proves compatibility with every
  `F`-algebra map `f : R →ₐ[F] S`, acting as `f` on `R` and as
  `id_E ⊗ f` on `E ⊗[F] R`.
- Assume moreover `FiniteDimensional E B`, `Algebra.IsCentral E B` and
  `IsSimpleRing B`, so that `B` is a central simple `E`-algebra.
  `relativeNorm F E B R : (R ⊗[F] B)ˣ →* (E ⊗[F] R)ˣ` is the reduced norm of `B`
  over `E` with coefficients in the commutative `E`-algebra `E ⊗[F] R`: it applies
  the published `Langlands.CentralSimple.reducedNormUnits E B (E ⊗[F] R)` after
  `tensorEquiv`. `relativeNorm_val` unfolds it, `relativeNorm_naturality` proves
  naturality in `R`, and `relativeNorm_includeRight` proves that on `1 ⊗ x`, for a
  unit `x` of `B`, it is `Nrd(x) ⊗ 1`, where `Nrd(x)` is
  `reducedNorm E B E (1 ⊗ x)`.
- `unitaryPoints τ R : Subgroup (R ⊗[F] B)ˣ` consists of the units `u` with
  `u * τ_R(u) = 1` (`mem_unitaryPoints`). The proof of the subgroup axioms uses that
  `u * τ_R(u) = 1` gives `τ_R(u) = u⁻¹`. `map_mem_unitaryPoints` proves stability
  under every `F`-algebra map of coefficients.
- `specialUnitaryPoints E τ R` is `unitaryPoints τ R ⊓ (relativeNorm F E B R).ker`:
  the units `u` with `u * τ_R(u) = 1` and relative reduced norm `1`
  (`mem_specialUnitaryPoints`). `map_mem_specialUnitaryPoints` and
  `specialUnitaryMap E τ f` give the coefficient change on these subgroups, with
  `specialUnitaryMap_val` computing it as `f ⊗ id_B` on underlying elements.

## Source

When `E` is a separable quadratic extension of `F` and `τ` acts on `E` by its
nontrivial automorphism (a unitary involution), these are the `R`-points of the
unitary group `U(B, τ)` and of the special unitary group `SU(B, τ)` of
Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998), §23.A,
"Unitary involutions" (printed p. 346, PDF p. 369):
`SU(B, τ)(R) = {b ∈ (B ⊗_F R)ˣ | τ_R(b) b = 1, Nrd_B(b) = 1}`, where `Nrd_B` is the
reduced norm of `B` over its centre `K = E`, extended to `K ⊗_F R`. Here the
coefficients are written on the left, `R ⊗[F] B`, and the unitary condition is
written `u τ_R(u) = 1`, which is equivalent to `τ_R(u) u = 1` for units. The
definitions themselves make no assumption on the degree of `E` or on how `τ` acts
on `E`; statements using them state those hypotheses.
