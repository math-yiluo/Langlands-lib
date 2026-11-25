# Relative ideles: the tensor-product model 𝔸_K ⊗_K L

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields the file models the adeles of `L` as `𝔸_K ⊗_K L` and the ideles of `L` as its unit group. In this model the inclusion of `I_K`, Galois conjugation and the idele norm become operations of linear algebra over `𝔸_K`. The main result identifies the Galois-fixed relative ideles with the image of `I_K` when `L/K` is Galois.

## Main declarations

- `RelativeAdeleRing K L` is `AdeleRing (𝓞 K) K ⊗[K] L`, and `RelativeIdeleGroup K L` is its group of units.
- `adeleInclusion`, `fieldInclusion`: the maps `a ↦ a ⊗ 1` and `x ↦ 1 ⊗ x`. `inclusion : IdeleGroup K →* RelativeIdeleGroup K L` is injective (`inclusion_injective`), and `principalIdele : Lˣ →* RelativeIdeleGroup K L` is the diagonal copy of `Lˣ`; `inclusion_principalIdele` says the two agree on `Kˣ`.
- `norm`: the relative idele norm to `IdeleGroup K`, defined as `Algebra.norm` over `𝔸_K`, that is, as a determinant. `norm_inclusion` gives `N(a) = a ^ [L : K]` for `a ∈ I_K`; `norm_principalIdele` says the norm of a principal idele is the principal idele of the field norm, via `norm_fieldInclusion`, computed with a base-changed basis.
- `conjugation σ`, `conjugationIdele σ`: `id ⊗ σ` on adeles and on ideles. They define the instance `relativeIdeleMulAction` of `L ≃ₐ[K] L` and the reducible def `relativeIdeleMulDistribMulAction`. `smul_inclusion` says base ideles are fixed; `smul_principalIdele` says the action on principal ideles is conjugation of `x`.
- `galoisAverage`: the averaging operator `z ↦ |G|⁻¹ Σ σ z`. For `L/K` Galois, it fixes invariant elements (`galoisAverage_eq_of_fixed`), and sends `a ⊗ x` to the image of `a · |G|⁻¹ Tr(x)` under `adeleInclusion` (`galoisAverage_tmul`), so every fixed relative adele comes from `𝔸_K` (`exists_adele_eq_of_galois_fixed`).
- `galoisFixedSubgroup` and `inclusion_range_eq_galoisFixedSubgroup`: for `L/K` Galois, the image of `I_K` is exactly the subgroup of relative ideles fixed by every `σ`. The proof applies the averaging result to `u` and `u⁻¹` and assembles a unit of `𝔸_K`.

## Points to watch

- `RelativeIdeleGroup` is the library's own model, not Mathlib's ideles of `L`; this file does not compare the two.
- The norm is the determinant over `𝔸_K`, not a product of local norms.
- The Galois action on relative ideles is an instance as a `MulAction`, but its `MulDistribMulAction` form is only a reducible def.
- Averaging divides by the order of the Galois group in `K`, which uses characteristic zero; the fixed-point statements need `IsGalois K L`, while most other results drop `NumberField L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/BaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `21a8007b927797db2625d9b9fe58f909d841512342709ad916de929467154e95`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
