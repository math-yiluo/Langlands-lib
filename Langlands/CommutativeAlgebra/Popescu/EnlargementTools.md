# Tools for the unit enlargement

Auxiliary lemmas in namespace `Langlands.CommutativeAlgebra.Popescu.Enlargement`, used by the
proof of `ArtinianUnitEnlargementStatement`. They use only the standard axioms.

- `flat_of_map_maximalIdeal`: let `D → D' → L` be local maps of local rings, with `D'` and `L`
  Noetherian, `L` flat over `D` and `𝔪_D D' = 𝔪_{D'}`. Then `L` is flat over `D'`.
  - By the Library's local flatness criterion (`Langlands.Algebra.localFlatnessCriterion`), it
    suffices that `𝔪_{D'} ⊗_{D'} L → L` is injective.
  - The comparison map `𝔪_D ⊗_D L → 𝔪_{D'} ⊗_{D'} L` is surjective because `𝔪_D` generates
    `𝔪_{D'}`.
  - It is compatible with the multiplication maps, and `𝔪_D ⊗_D L → L` is injective by flatness.
- `exists_pow_eq_one`: in a local ring of characteristic `p` with nilpotent maximal ideal, if
  `u ≡ 1` then `u^{p^N} = 1` for some `N` (Frobenius on `1 + (u − 1)`).
- `exists_pow_mem_range`: if `ψ(x)ℓ ≡ 1` for a local `ψ`, then `ℓ^{p^N}` lies in the image of `ψ`.
- `isAdicComplete_of_isNilpotent`: a local ring with nilpotent maximal ideal is `𝔪`-adically
  complete (Hausdorff and precomplete, since `𝔪^n = 0` for large `n`). Mathlib then supplies the
  `HenselianLocalRing` instance used for Hensel's lemma in `caseA`.
- `isNilpotent_maximalIdeal`: the maximal ideal of an Artinian local ring is nilpotent (it is the
  Jacobson radical, `IsArtinianRing.isNilpotent_jacobson_bot`).
- `kaehler_basis_of_formallyEtale`: a differential basis of `Ω_{F/k}` stays a basis in
  `Ω_{F'/k}` for a formally étale field extension `F'/F`. This is base change of the basis along
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.
- `D_pow_char`: `d(x^p) = 0` in `Ω_{F/k}` when `F` has characteristic `p`.
- `exists_pth_power_preimage`: let `ψ : D' → L` be local, `L` of characteristic `p` with nilpotent
  maximal ideal, `ℓ` a unit, and `ψ(x) ≡ ℓ^e` with `e > 0`. Then `ψ(w^p) = ℓ^Q` for some `w` and
  some `Q > 0`. Apply `exists_pow_mem_range` to `ℓ^{-e}`, invert the preimage, and take a
  `p`-th power.
