# Star-fixed weights and coset sums of star translates

This module supplies the lattice side of the transfer clause for the Tits obstruction
(Task 7603, clause 3): the subgroups of star-fixed integral weights and the coset sum
`∑_{σ ∈ Γ/Γ_E} σ ⋆ λ`, with independence of representatives, star invariance, additivity
and the multiplicity of each translate. It constructs no Tits algebra, Brauer class or
corestriction, and no base change of the group.

## Generic coset sums

For a group `Γ`, a module `M` over a semiring `R`, an action `ρ : Γ →* (M ≃ₗ[R] M)` and a
subgroup `H`:

* `equivCosetSum ρ H m := ∑ᶠ q : Γ ⧸ H, ρ q.out m`: one term for each left coset `q = gH`,
  evaluated at the chosen representative `q.out` (Mathlib's `Quotient.out`). A translate
  given by several cosets is counted once for each of them. The sum is a `finsum`. When
  `Γ ⧸ H` is finite it is the ordinary finite sum (`equivCosetSum_eq_sum`). When `Γ ⧸ H` is
  infinite, Mathlib's `finsum` convention makes it `0`. Independence of representatives
  (sections, set transversals and `Finset` transversals), `equivCosetSum_zero` and the
  exact-stabilizer orbit identity `equivCosetSum_equivStabilizer` hold at arbitrary index.
  The remaining results assume `Γ ⧸ H` finite (`[Finite (Γ ⧸ H)]` or
  `[Fintype (Γ ⧸ H)]`), and the bullets below state this with each result that uses it.
* `equivStabilizer ρ m`: the subgroup `{g | ρ g m = m}`.

Results, for `m` fixed by every element of `H`:

* `apply_eq_of_coset_eq`: `ρ g m` depends only on the coset `gH`.
* Independence of representatives. `finsum_section_eq_equivCosetSum`: any function
  `s : Γ ⧸ H → Γ` with `s q ∈ q` for every `q` gives the same sum.
  `finsum_transversal_eq_equivCosetSum` and `sum_transversal_eq_equivCosetSum`: the same
  holds for a left transversal `S` of `H` (Mathlib's `Subgroup.IsComplement S H`), given as
  a set or as a `Finset`.
* `equivCosetSum_add`: additivity, for `Γ ⧸ H` finite. It holds for all `m, m'`, fixed or
  not, because the representatives are fixed. `equivCosetSum_zero` holds at arbitrary
  index.
* `apply_equivCosetSum`: invariance, `ρ g (equivCosetSum ρ H m) = equivCosetSum ρ H m` for
  every `g ∈ Γ`, for `Γ ⧸ H` finite. The proof reindexes the sum by the permutation
  `q ↦ g⁻¹ • q` of `Γ ⧸ H` and uses independence of representatives.
* `equivCosetSum_equivStabilizer`: over the full stabilizer, at arbitrary index, the coset
  sum is the `finsum` over the orbit `{ρ g m}`, each element once (`q ↦ ρ q.out m` is
  injective on `Γ ⧸ Stab(m)` with range the orbit).
* `equivCosetSum_eq_relIndex_smul`: multiplicities. For `Γ ⧸ H` finite, the coset sum is
  `[Stab(m) : H] • ∑_{μ ∈ orbit of m} μ`. The proof uses Mathlib's
  `Subgroup.quotientEquivProdOfLE`, `Γ ⧸ H ≃ (Γ ⧸ Stab(m)) × (Stab(m) ⧸ H)`.
* `equivCosetSum_eq_index_smul`: for `Γ ⧸ H` finite, if `m` is fixed by all of `Γ`, the
  coset sum is `[Γ : H] • m`.

## Star-fixed weights

Let `k ⊆ K` be fields, `G` an affine, locally finite type group scheme over `Spec k` and
`d : GaloisPinningData k K G` (Library, `Reductive/StarAction`), with split maximal torus
`T_K` and full star action `d.starAction : (K ≃ₐ[k] K) →* basedRootDatumAut`. The
integral weights are `characterLattice d.toSplitPinning.torus`, the character lattice of
`T_K`.

* `starWeightHom d`: the star action on integral weights, `σ ↦ (d.starAction σ).weightEquiv`,
  as a homomorphism to `ℤ`-linear automorphisms (Mathlib's `RootPairing.Equiv.weightHom`).
* `fixedWeights d H`: for a subgroup `H` of `K ≃ₐ[k] K`, the additive subgroup of weights
  `λ` with `(d.starAction σ).weightEquiv λ = λ` for every `σ ∈ H`.
* `starFixedWeights d := fixedWeights d ⊤`: the weights fixed by the star action of every
  automorphism. The Tits obstruction is defined on this subgroup. No condition on the
  action on vertices is imposed (`mem_starFixedWeights`).
* `fixedWeights_antitone`, `starFixedWeights_le_fixedWeights`,
  `mem_fixedWeights_iff_le_equivStabilizer`.

## The coset sum `∑_{σ ∈ Γ/Γ_E} σ ⋆ λ`

For an intermediate field `E` of `K/k`, `Γ_E = E.fixingSubgroup` is the subgroup of
`K ≃ₐ[k] K` fixing `E` pointwise.

* `cosetSum d E λ := equivCosetSum (starWeightHom d) E.fixingSubgroup λ`, that is
  `∑ᶠ q : (K ≃ₐ[k] K) ⧸ Γ_E, (d.starAction q.out).weightEquiv λ` (`cosetSum_def`). It uses
  one representative of each left coset and counts a weight again when different cosets
  give the same weight. It is defined for every `λ`. The results below assume
  `λ ∈ fixedWeights d Γ_E`, which makes the sum independent of the representatives.
* `fixingSubgroup_finiteIndex`, `finite_quotient_fixingSubgroup`: if `K/k` is Galois and
  `E/k` is finite, `Γ_E` has finite index. This follows from Mathlib's
  `IntermediateField.finrank_eq_fixingSubgroup_index`, `[E : k] = [Γ : Γ_E]`. For a
  separable closure `K` of `k`, `IsGalois k K` is a Mathlib instance
  (`IsSepClosure.isGalois`).
* `finsum_section_eq_cosetSum`, `finsum_transversal_eq_cosetSum`,
  `sum_transversal_eq_cosetSum`: independence of representatives, for any choice of
  representatives and any left transversal of `Γ_E` (as a set, or as a `Finset`), at
  arbitrary index.
* `cosetSum_mem_starFixedWeights`: star invariance. For `K/k` Galois, `E/k` finite and
  `λ` fixed by `Γ_E`, the coset sum is fixed by the star action of every automorphism.
* `cosetSum_zero`: the coset sum of `0` is `0` (no hypothesis on `K/k` or `E`).
* `cosetSum_add`: for `K/k` Galois and `E/k` finite, the coset sum is additive on all
  weights.
* `cosetSumHom d E : fixedWeights d Γ_E →+ starFixedWeights d`: for `K/k` Galois and
  `E/k` finite, the coset sum as an additive map (`coe_cosetSumHom_apply`).
* `cosetSum_eq_relIndex_smul`: multiplicities. For `K/k` Galois, `E/k` finite and `λ` fixed
  by `Γ_E`, each star translate of `λ` occurs `[Stab(λ) : Γ_E]` times, where
  `Stab(λ) = equivStabilizer (starWeightHom d) λ`.
* `cosetSum_eq_finsum_orbit`: if `Γ_E` is the full star stabilizer of `λ`, the coset sum is
  the `finsum` over the star orbit of `λ`, each weight once (at arbitrary index, with no
  hypothesis on `K/k` or `E`).
* `cosetSum_of_mem_starFixedWeights`: for `K/k` Galois, `E/k` finite and a star-fixed `λ`,
  the coset sum is `[E : k] • λ`. The Galois hypothesis identifies the number of cosets of
  `Γ_E` with `[E : k]`; without it the formula can fail (for `K = E = ℚ(∛2)` over `ℚ` the
  automorphism group is trivial and the sum is `λ`).

## Provenance

Internal. The construction follows the sum `c = ∑_{θ ∈ Θ} θ(c₁)` in Tits (1971),
Proposition 5.1 (J. reine angew. Math. 247, p. 207), where `Θ` is a system of
representatives of `Γ/Γ₁`. Tits takes for `Γ₁` the stabilizer of `c₁` and for `k₁` its
fixed field, and states the result for `c₁` in his group `C*`. Here the sum is taken in
the actual integral character lattice of the split torus, as the task requires. Here `Γ_E` may be any subgroup
`Gal(K/E)` of finite index contained in the stabilizer, as clause 3 of Task 7603 requires,
and multiplicities are counted.

`cosetSum_eq_finsum_orbit` is the integral-weight analogue of the norm sum of Tits's
Proposition 5.1, not Tits's case itself. The stabilizers differ. Here it is the star
stabilizer of the weight `λ` in the integral character lattice. Tits uses the stabilizer of
the central class `c₁ ∈ C*`. These stabilizers, and so the fields they define, can differ.
For the Weil restriction of split `SL₂` from a separable quadratic extension, the
nontrivial star element swaps the two weight coordinates. The weight `(2, 0)` then has a
two-element orbit in `ℤ²`, while its class is `0` in `(ℤ/2)²` and is fixed. The Brauer
corestriction identity `β_{G,k}(c) = Cor(β_{G,k₁}(c₁))` is the content of Tits's
Proposition 5.1 itself, and it is not proved in this module.
The proofs are elementary group theory with Mathlib's quotient, transversal and `finsum`
API. This module defines the domain `starFixedWeights` of the obstruction and the
left-hand side of the transfer identity. The obstruction and the identity itself are
outside this module.
