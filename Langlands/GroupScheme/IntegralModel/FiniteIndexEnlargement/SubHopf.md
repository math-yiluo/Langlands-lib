# Hopf subalgebras of flat Hopf algebras

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. It lives in namespace
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf`.

## Content

Let `R` be a commutative ring, `A` a Hopf algebra over `R`, and `B : Subalgebra R A`. Write
`ι : B →ₗ[R] A` for the inclusion and `ι₂ = ι ⊗ ι : B ⊗[R] B →ₗ[R] A ⊗[R] A`. The module
assumes:

- `A` and `B` are flat over `R` (`[Module.Flat R A] [Module.Flat R B]`);
- `hΔ : ∀ x : B, comul (x : A) ∈ LinearMap.range (ι₂ B)`;
- `hS : ∀ x : B, antipode (x : A) ∈ B`.

Under these assumptions it constructs:

- `map_injective_of_flat`: `TensorProduct.map f g` is injective when `f` and `g` are injective
  and the modules `M` and `Q` are flat (write it as `rTensor f ∘ lTensor g`). So `ι₂` and
  `ι ⊗ ι₂` are injective (`ι₂_injective`, `ι₃_injective`).
- `comulLin`: the comultiplication of `B`, namely `comul ∘ ι` corestricted to the range of `ι₂`
  and pulled back along the injective `ι₂`. Its defining property is `ι₂_comulLin`:
  `ι₂ (comulLin x) = comul (x : A)`. `counitLin` is `counit ∘ ι`.
- `coalgebra`, `bialgebra`, `hopfAlgebra`: the structures on `B`, given as `@[reducible]` defs
  rather than instances. Each axiom is checked after applying an injective map (`ι₃`, `ι`, or
  `ι` tensored with `R`), using the corresponding axiom of `A`. The compatibility lemmas
  `map_ι₂_ι_rTensor`, `map_ι_ι₂_lTensor`, `map_ι_ι₂_assoc`, `lTensor_ι_rTensor_counit`,
  `rTensor_ι_lTensor_counit`, `ι_mul'_rTensor` and `ι_mul'_lTensor` move the structure maps
  across the inclusions. `comulLin_mul` and `comulLin_one` use that `ι₂` is multiplicative
  (`ι₂_mul`, `ι₂_one`).
- `valBialgHom`: the inclusion `B →ₐc[R] A` as a bialgebra homomorphism for this Hopf
  structure. `valBialgHom_apply` and `toAlgHom_valBialgHom` say its underlying algebra map is
  `B.val`. `comul_val` says `comul (x : A) = ι₂ (comul x)`.

## Provenance and license

This module adapts the `TakK` section of the Anthropic FLT file
`P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean`
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`). That file is published in this Library as
`Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed`.
It is © 2026 Anthropic, PBC, under the Apache License 2.0. The license and notices are retained
in [LICENSE](../../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION.md](../../../../licenses/Anthropic-FLT/ATTRIBUTION.md). The Lean file carries an
attribution header.

Changes from the source:

- the base field `k` is replaced by an arbitrary commutative ring `R`. Flatness of `A` and `B`
  replaces the field hypothesis in the injectivity of tensor maps.
- the comultiplication hypothesis is stated directly as membership in the range of `ι₂`, not in
  the span of pure tensors;
- the deprecated `TensorProduct.induction_on` is replaced by `TensorProduct.inductionOn`, which
  has no zero case.
- the bialgebra inclusion `valBialgHom` and its lemmas are new.

No mathematical statement from an external source is asserted.
