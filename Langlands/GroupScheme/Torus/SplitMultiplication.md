# Multiplication by a nonzero integer on a split torus

Module `Langlands.GroupScheme.Torus.SplitMultiplication`.

This is an internal helper of the proof that maximal split tori lift under central
isogenies (`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`). It records
a standard fact: on a split torus `G_m^r`, the `n`-th power map with `n ≠ 0` is faithfully
flat. On coordinate rings it is the inclusion `R[ℤ^r] → R[ℤ^r]` induced by `n : ℤ^r → ℤ^r`,
and `R[ℤ^r]` is a free module over the image ring.

## Declarations

* `Diagonalizable.restrictMap_smul_id R n`: on the diagonalizable group scheme `D(Λ)` over a
  commutative ring `R`, the homomorphism `restrictMap R (n • AddMonoidHom.id Λ)` equals
  `multiplication (groupScheme R Λ).toGrp n` (`Langlands.AbelianScheme.Multiplication`).
  The proof compares the two maps on the universal point `𝟙`.
  `Corepresented.pointsEquiv` identifies points of `D(Λ)` with characters `Λ → Γ(T)ˣ` as
  groups. `pointsEquiv_restrictMap` computes the left side as `χ ↦ χ ∘ (n • ·)`, and
  `points_multiplication` computes the right side as `χ ↦ χ ^ n`.
* `Diagonalizable.smul_id_injective hn`: for `n ≠ 0`, `n • id` is injective on `I → ℤ`.
* `IsSplitTorus.flat_and_surjective_multiplication hS hn`: let `R` be a nonzero commutative
  ring, `S` a commutative group scheme over `Spec R` that is a split torus
  (`IsSplitTorus S.toGrp`), and `n ≠ 0`. Then the underlying scheme map of
  `multiplication S.toGrp n` is flat and surjective. The proof chooses an isomorphism
  `S ≅ splitTorus I ≅ D(I → ℤ)` (the latter is `Diagonalizable.splitIso`). It transports
  multiplication by `n` along it with `multiplication_naturality`, and applies
  `Diagonalizable.flat_and_surjective_restrictMap` to the injective map `n • id`.
