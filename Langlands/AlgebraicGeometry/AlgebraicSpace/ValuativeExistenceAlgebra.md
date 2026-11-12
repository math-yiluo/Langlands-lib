# Commutative algebra for the valuative existence criterion

Author: Worker 198.

Helper module for the proof of `SpaceValuativeExistenceStatement` (Stacks Project, Lemma
67.42.3, Tag 0A3Y, (1) ⇒ (3)), given in `SpaceValuativeExistenceProof.lean`. It contains no
statement from the literature. It collects the ring-theoretic facts used in the descent step
(`ValuativeExistenceCore.lean`). All results are standard; the proofs are short arguments from
Mathlib.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence`.

Throughout, `A` is a domain with fraction field `K` (`[IsFractionRing A K]`) and `P` is an
`A`-algebra.

- `exists_smul_eq_one_tmul`: every `t ∈ K ⊗[A] P` has a common denominator, i.e. there are
  `a ∈ A`, `a ≠ 0`, and `p ∈ P` with `a • t = 1 ⊗ p`. Proof by induction on `t`
  (`TensorProduct.inductionOn`): a pure tensor `(n/d) ⊗ p` gives `d • ((n/d) ⊗ p) = 1 ⊗ n•p`
  (`IsLocalization.surj`); for a sum one multiplies the two denominators.
- `map_eq_zero_of_tmul`: let `R` be a `K`-algebra (compatible with `A`), `H : K ⊗[A] P → R` an
  `A`-algebra map and `I` an ideal of `K ⊗[A] P`. If `H` kills every element of `I` of the form
  `1 ⊗ p`, then `H` kills `I`. For `t ∈ I` write `a • t = 1 ⊗ p`; then `1 ⊗ p ∈ I`, so
  `a • H t = 0`, and `a` acts invertibly on the `K`-algebra `R`.
- `flat_of_injective`: over a valuation ring `A`, an `A`-module `D` admitting an injective
  `A`-linear map into a `K`-vector space `B` is flat. Mathlib's
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` (valuation rings are Bézout domains) reduces
  this to torsion-freeness, and a torsion element of `D` maps to a torsion element of `B`, which
  is zero.
- `includeRight_injective`: for a flat `A`-algebra `M`, the map `M → K ⊗[A] M`, `m ↦ 1 ⊗ m`, is
  injective. It is `A ⊗[A] M → K ⊗[A] M` (tensoring the injection `A → K` with the flat module
  `M`) composed with `M ≅ A ⊗[A] M`. Only `IsFractionRing A K` is needed, not that `A` is a
  domain.
- `faithfullyFlat_of_map_maximalIdeal_ne_top`: over a local ring `A`, a flat `A`-algebra `D` with
  `𝔪_A D ≠ D` is faithfully flat. By `Module.FaithfullyFlat.iff_flat_and_proper_ideal` it
  suffices that `I D ≠ D` for every proper ideal `I`, and `I ⊆ 𝔪_A`.
