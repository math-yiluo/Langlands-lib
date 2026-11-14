# Fibrewise regular elements of flat local extensions

Authors: Worker 5705 (Lean); Markdown by Worker 22.

Worker 5705 wrote this module for task `07219dde-fd87-48cf-83be-db16cbb3707c`
(Task 5705), as part of their proof work on that task. Worker 22 carries it
unchanged in the candidate proving
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement`,
because the module `Langlands.AlgebraicGeometry.Picard.LocalEquationCartier`
used there imports it. By agreement between the two workers, the first proof
candidate that uses these modules carries them. All declarations are in the
namespace `Langlands.CommutativeAlgebra.FibrewiseRegular`. The module imports
only Mathlib.

Provenance: internal, following S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`), Lemma 3.4, (iii) ⟹ (i),
proof on p.23. Kleiman uses the local criterion of flatness ([SGA 1, Thm. 5.6]).
This module proves the special case needed here directly, by induction on the
power of the maximal ideal killing a module and Krull's intersection theorem.

Throughout, `A → B` is a ring map and `mulB b : B → B` is multiplication by
`b`, as an `A`-linear map.

## Modules killed by powers of the maximal ideal

Let `A` be local with maximal ideal `𝔪` and let `b : B` be regular on the
closed fibre, that is, `(mulB b) ⊗ (A ⧸ 𝔪)` is injective.

- `injective_rTensor_of_isTorsionBySet`: then `(mulB b) ⊗ V` is injective for
  every `A`-module `V` killed by `𝔪`. Proof: `V` is a vector space over
  `A ⧸ 𝔪`, so `B ⊗ V` is a direct sum of copies of `B ⊗ (A ⧸ 𝔪)`
  (`TensorProduct.finsuppRight`).
- `rTensor_mulB_lTensor`: multiplication by `b` commutes with `B ⊗ f` for
  every `A`-linear `f`.
- `injective_rTensor_of_isTorsionBySet_pow` (with `B` flat over `A`): then
  `(mulB b) ⊗ P` is injective for every `A`-module `P` killed by `𝔪 ^ n`.
  Proof by induction on `n`, using the exact sequence
  `0 → 𝔪 ^ n P → P → P ⧸ 𝔪 ^ n P → 0`, which stays exact after `B ⊗ -`
  because `B` is flat.

## Finite modules (Krull)

Let moreover `B` be local and noetherian, `A → B` a local homomorphism and `B`
flat over `A`.

- `map_maximalIdeal_le`: `𝔪 B` lies in the maximal ideal of `B`.
- `injective_rTensor_of_finite`: if `b` is regular on the closed fibre, then
  `(mulB b) ⊗ P` is injective for every finite `A`-module `P`. Proof: an
  element of the kernel lies in `(𝔪 B) ^ n (B ⊗ P)` for every `n` (apply the
  previous lemma to `P ⧸ 𝔪 ^ n P`). The intersection of these submodules is
  zero by Krull's intersection theorem
  (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`), as `B ⊗ P` is a finite
  module over the noetherian local ring `B`.
- `isSMulRegular_of_fibre`: such a `b` is regular in `B` (case `P = A`).
- `flat_quotient_of_fibre`: such a `b` has `B ⧸ (b)` flat over `A`. Proof:
  by the ideal criterion (`Module.Flat.iff_lTensor_injective'`): for an ideal
  `I` of `A`, chase the exact sequence `B → B → B ⧸ (b) → 0` (multiplication
  by `b`, then the quotient map) tensored with `I`, `A` and `A ⧸ I`, using
  injectivity of multiplication by `b` on `B ⊗ (A ⧸ I)` and flatness of `B`.

## Fibre rings

- `injective_rTensor_quotient_iff`: for an ideal `I` of `A`, `(mulB b) ⊗ (A ⧸ I)`
  is injective if and only if `b` is regular on `B ⧸ I B`
  (`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`).

## The affine criterion

Let `R` be a noetherian `A`-algebra, flat over `A`.

- `localStep`: let `P` be a prime of `R`, `p = P ∩ A`, and `s : R` regular on
  the fibre local ring `R_P ⧸ p R_P`. Then `s` is regular in `R_P`, and
  `R_P ⧸ (s)` is flat over `A`. Proof: apply the two previous results to the
  flat local homomorphism `A_p → R_P` (`Localization.localRingHom`,
  `RingHom.Flat.localRingHom`), then use transitivity of flatness
  `A → A_p → R_P ⧸ (s)`.
- `regular_and_flat_quotient`: if `s : R` is regular on `R_P ⧸ (P ∩ A) R_P` for
  every maximal ideal `P` of `R`, then `s` is regular in `R` and `R ⧸ (s)` is
  flat over `A`. Regularity: if `s x = s y` with `x ≠ y`, take a maximal ideal
  containing the annihilator of `x - y` and localize there. Flatness: flatness
  is local at the maximal ideals of `R` (`Module.flat_of_isLocalized_maximal`).
