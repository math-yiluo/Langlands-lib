# The double-coset formula for the transfer along a homomorphism

Module `Langlands.GroupTheory.TransferDoubleCoset`, namespace
`Langlands.GroupTheory.Transfer`.

## Setting

`H` is a finite-index subgroup of a group `G`, `A` is a commutative group,
`ϕ : H →* A`, and `MonoidHom.transfer ϕ : G →* A` is Mathlib's transfer. `ψ : L →* G`
is a group homomorphism, `ι` is a finite index type, and `t : ι → G` chooses
representatives of the double cosets `ψ(L) \ G / H`:

- `hcover : ∀ g, ∃ i l, ∃ h ∈ H, g = ψ l * t i * h` (every element lies in some
  `ψ(L) t_i H`);
- `hdisj : ∀ i j l, ∀ h ∈ H, t j = ψ l * t i * h → i = j` (distinct indices give
  distinct double cosets).

These two hypotheses have the same shape as the double-coset hypotheses of the
Mackey formula `ExactGrothendieckGroup.continuousRestrict_continuousInduceAlong`.

## Statements

- `section_factor_mem`: for a section `τ : G ⧸ H → G` (`(τ q : G ⧸ H) = q`), the
  factor `(τ q)⁻¹ * g * τ (g⁻¹ • q)` lies in `H`.
- `transfer_eq_prod_section`: `transfer ϕ g = ∏ q, ϕ ⟨(τ q)⁻¹ * g * τ (g⁻¹ • q), _⟩` for
  every section `τ`. This is the defining coset-product formula with an arbitrary
  choice of representatives.
- `doubleCosetMap ψ t K hK : (Σ i, L ⧸ K i) → G ⧸ H`, `(i, l K_i) ↦ ψ l t_i H`, where
  `K i` is any subgroup of `L` with `hK : l ∈ K i ↔ (t i)⁻¹ * ψ l * t i ∈ H` (the
  stabilizer of the coset `t_i H` under `L` acting through `ψ`). Lemmas:
  `doubleCosetMap_mk`, `doubleCosetMap_eq_out`, `doubleCosetMap_smul` (it is
  `L`-equivariant) and `doubleCosetMap_bijective` (from `hcover` and `hdisj`).
- `transfer_comp_eq_prod_of_conj`: if `[∀ i, (K i).FiniteIndex]` and
  `ϕ' i : K i →* A` satisfies `ϕ' i k = ϕ ⟨(t i)⁻¹ * ψ k * t i, _⟩`, then
  `transfer ϕ (ψ y) = ∏ i, transfer (ϕ' i) y`.
- `transfer_comp_eq_prod`: the same with `K i` the comap of `H` under
  `l ↦ (t i)⁻¹ * ψ l * t i` and `ϕ' i = ϕ ∘ (that map restricted)`; the finite-index
  instances come from Mathlib's comap instance.
- `transfer_comp_eq_prod_of_normal`: for normal `H`, every `K i` is `H.comap ψ` and
  `transfer ϕ (ψ y) = ∏ i, transfer ((ϕ.comp (conjInv (t i))).comp (ψ.subgroupComap H)) y`,
  with `conjInv` from `Langlands.ClassField.Global.RelativeWeilTransfer`.

## Provenance

This is the standard double-coset (Mackey) formula for the group-theoretic transfer,
stated here along a homomorphism `ψ` rather than a subgroup inclusion. It is internal
infrastructure for the local restriction formula of relative Weil groups (the transfer
part of Tate (1979), (1.6.1) and (2.3.5)), written for this project; no statement or
proof is taken from a specific source.

## Proof

`transfer_eq_prod_section` applies `MonoidHom.transfer_def` to the left transversal
`Set.range τ` (`isComplement_range_left`) and evaluates both transversals with
`IsComplement.leftQuotientEquiv_apply` and `smul_apply_eq_smul_apply_inv_smul`.

For `transfer_comp_eq_prod_of_conj`, `doubleCosetMap` is well defined because
`a⁻¹ b ∈ K i` gives `(ψ a t_i)⁻¹ (ψ b t_i) ∈ H`; it is injective by `hdisj` followed by
`hK`, and surjective by `hcover`. With the equivalence `e` it defines, the section
`τ (e (i, β)) = ψ (β.out) * t i` is used in `transfer_eq_prod_section` for `G`; the
product is reindexed along `e` and split with `Fintype.prod_sigma`. By equivariance
`(ψ y)⁻¹ • e (i, β) = e (i, y⁻¹ • β)`, so the factor at `(i, β)` is
`ϕ ⟨(t i)⁻¹ ψ(β.out⁻¹ y (y⁻¹ • β).out) t i, _⟩ = ϕ' i ⟨β.out⁻¹ y (y⁻¹ • β).out, _⟩`,
and the inner product over `β` is `transfer (ϕ' i) y` by `transfer_eq_prod_section`
for `L` with the section `Quotient.out`. The two corollaries supply `K i`, `hK` and
`ϕ'`; in the normal case `hK` follows from `Subgroup.Normal.conj_mem` in both
directions.
