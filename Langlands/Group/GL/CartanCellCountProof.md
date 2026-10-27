# Counting left cosets in an antidominant Cartan double coset: proof

Author: Worker 23.

The closing theorem `Langlands.GeneralLinear.CartanQuotient.cartanCellCount`
proves exactly the published
`Langlands.GeneralLinear.CartanQuotient.CartanCellCountStatement.{uF}` of
[CartanCellCountStatement](CartanCellCountStatement.md), keeping the field
universe `uF`. It adds no hypothesis and covers every prime `p`, field
`F : PadicField.{uF} p`, topological realization `T` and rank `n`, including
rank zero. The statement's Lean/Markdown pair is unchanged.

The proof takes the constant `c = q ^ (n * n)`, where
`q = T.residueCardinality` is the cardinality of the residue field. For an
antitone `lam` it takes for `R` a set of coset representatives, in `K`, of an
entrywise congruence subgroup `S_lam` of `K`. In the notation below,

```text
R.card ≤ [K : S_lam] = [K : S_0] · [S_0 : S_lam] ≤ q^(n*n) · q^(degree lam)
       = q^(n*n) · (delta T lam)⁻¹.
```

All auxiliary declarations live in the namespace
`Langlands.GeneralLinear.CartanQuotient.CellCount`. Throughout, `K` is
`maximalCompact T n`, `a(μ)` is `representative T μ`, `v` is
`T.discreteValuation`, and `ϖ` is
`LocalFactor.PadicAbelian.uniformizerUnit T`, with `v (ϖ ^ k) = exp (-k)`.

## Valuation levels and residues

`Level T e x` means `v x ≤ WithZero.exp (-e)`, that is, `x ∈ ϖ^e O`. Levels
are preserved by sums, negation, subtraction and finite sums, and they add
under multiplication. An element of level `e` has every level `f ≤ e`. Level
zero means `v x ≤ 1`.
`level_uniformizer_mul_iff` says that `ϖ^(-k) x` has level `e` exactly when `x`
has level `e + k`.

`res T x` is the residue `T.residue ⟨x, _⟩` of `x` when `x ∈ T.Integers`, and
zero otherwise. On elements with `v x ≤ 1` it is additive (`res_add`).
`res_eq_zero_iff` says such an `x` has residue zero exactly when it has level
one. The proof identifies the maximal ideal with the non-units, which are the
elements of valuation `< 1` by `Valuation.Integer.not_isUnit_iff_valuation_lt_one`.
It then transports along
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` to `ℤᵐ⁰`, where
`y < 1 ↔ y ≤ exp (-1)`. Consequently two integral elements with equal residues
differ by an element of level one (`level_sub_of_res_eq`).

`mem_maximalCompact_iff` characterizes `K`: `g ∈ K` exactly when all entries
of `g` and of `g⁻¹` have valuation at most one. The reverse direction assembles
the two integral matrices into a unit of `Matrix (Fin n) (Fin n) O`.

## Entrywise congruence subgroups

For `μ : Fin n → ℤ` the entry level is `lev μ i j = 1 + max 0 (μ i - μ j)`. It
satisfies `lev μ i j + 1 ≤ lev μ i k + lev μ k j` (`lev_add_one_le`).
`Congr T μ A` says that every entry `(A - 1) i j` has level `lev μ i j`. From
`AB - 1 = (A - 1)(B - 1) + (A - 1) + (B - 1)` (`mul_sub_one`) and
`lev_add_one_le`, the cross term of two congruent matrices has level
`lev μ i j + 1` (`cross_level`), so `Congr` is closed under products.

`levelSubgroup T μ`, written `S_μ` here, consists of the invertible `g` with
both `g` and `g⁻¹` congruent at the levels of `μ`. `S_0` is the principal
congruence subgroup of level one. Every `S_μ` lies in `K`
(`levelSubgroup_le_maximalCompact`) and in `S_0` (`levelSubgroup_le_zero`).

`conj_mem_maximalCompact` shows `a(μ)⁻¹ g a(μ) ∈ K` for `g ∈ S_μ`, for every
`μ`. The `(i, j)` entry of the conjugate is `ϖ^(-μ i) g_ij ϖ^(μ j)`
(`representative_conj_apply`, via `Iwasawa.torus_inv` and
`Iwasawa.diagonalUnits_mul_mul_apply`), of valuation
`exp (μ i - μ j) · v g_ij`. Off the diagonal this is at most
`exp (μ i - μ j - lev μ i j) ≤ 1`, and diagonal entries of a congruent matrix
are integral. The same bound applies to `g⁻¹`, so `mem_maximalCompact_iff`
gives the claim. The proof does not identify `S_μ` with any intersection of
conjugate subgroups; it uses only this containment.

## The index of `S_0` in `K`

`finite_quotient_of_fibres` is a general counting lemma. If a map `f : G → X`
into a finite type has `x⁻¹ y ∈ H` whenever `f x = f y`, then `G ⧸ H` is finite
with at most `Nat.card X` elements. The proof maps the range of `f` onto the
quotient by choosing preimages.

The lemma is applied to the entrywise residue map
`K → (Fin n → Fin n → T.ResidueField)`. The residue field is finite by
`T.finite_residueField`. If `x, y ∈ K` have equal residues, then
`x⁻¹ y - 1 = x⁻¹ (y - x)` has all entries of level one (`congr_zero_inv_mul`),
and the same holds for `(x⁻¹ y)⁻¹ = y⁻¹ x`. Hence `x⁻¹ y ∈ S_0`.
`relIndex_levelSubgroup_zero` concludes that `S_0.relIndex K` is nonzero and at
most `q ^ (n * n)`.

## Fundamental-coweight steps

`coweight n m` is `ω_m`, equal to `1` on the coordinates `i < m` and `0`
elsewhere. `Block n m` is the type of entry positions `(i, j)` with
`i < m ≤ j`. For antitone `μ`, `lev_add_coweight` shows that
`lev (μ + ω_m) i j` equals `lev μ i j + 1` on `Block n m` and `lev μ i j`
elsewhere.

`scaledEntry T μ A i j` is `ϖ^(-lev μ i j) (A - 1)_ij`. It is integral when
`A` is congruent at the levels of `μ`, and its residue vanishes exactly when
`(A - 1)_ij` has level `lev μ i j + 1`. For congruent `A, B` the residue of the
scaled entry of `AB` is the sum of those of `A` and `B`
(`res_scaledEntry_mul`). The scaled cross term has level one, so its residue
vanishes.

`blockMap T μ m` is the resulting monoid homomorphism
`S_μ →* Multiplicative (Block n m → T.ResidueField)`, which records the residues
of the scaled entries on `Block n m`. For antitone `μ`, `blockMap_ker`
identifies its kernel with `S_(μ + ω_m)` inside `S_μ`. The kernel is a
subgroup, so `g⁻¹` lies in it whenever `g` does, which gives the condition on
`g⁻¹`. Since `Subgroup.index_ker` equates the index of a kernel with the
cardinality of the range, `relIndex_add_coweight` shows that
`S_(μ + ω_m).relIndex S_μ` is nonzero and at most `q ^ Nat.card (Block n m)`.

## Induction on the degree

The existing `CartanQuotient.degree_nonneg` from
[CartanQuotientLawsProof](CartanQuotientLawsProof.md) gives
`0 ≤ degree lam` for antitone `lam`. Degree is additive
(`degree_add`), and `degree_coweight` gives
`degree ω_m = Nat.card (Block n m)`. If an antitone `lam` is not constant,
`exists_descent` gives `0 < m < n` with `lam m < lam (m - 1)`, and then
`lam - ω_m` is antitone (`antitone_sub_coweight`).

`relIndex_levelSubgroup_le` proves, by induction on a natural bound `N` with
`degree lam < N`, that for antitone `lam` the index `S_lam.relIndex S_0` is
nonzero and, as a real number, at most `q ^ degree lam`. For constant `lam`,
`S_lam = S_0` and the degree is zero. Otherwise write `lam = μ + ω_m` as above.
`Block n m` contains `(m - 1, m)`, so `degree μ < degree lam`. The induction
hypothesis for `μ` and the step bound combine through
`Subgroup.relIndex_mul_relIndex`.

## Assembly

`cartanCellCount` chooses `c = q ^ (n * n)`. Given an antitone `lam`, it sets
`S = S_lam`. The two index bounds and `Subgroup.relIndex_mul_relIndex` show that
`S.subgroupOf K` has finite index, with
`S.relIndex K ≤ q ^ degree lam · q ^ (n * n)`. `R` is the image of
`Quotient.out` over all cosets of `S.subgroupOf K` in `K`. Its cardinality is
at most the number of cosets, which is `S.relIndex K`. The last bound is
`q ^ (n * n) · (delta T lam)⁻¹`, since `delta T lam = q ^ (-degree lam)`.

For the covering, take `k₁, k₂ ∈ K`. `QuotientGroup.mk_out_eq_mul` gives
`h ∈ S` with `r = k₁ h`, where `r ∈ R` is the representative of the coset of
`k₁`. With `k = a(lam)⁻¹ h⁻¹ a(lam) k₂`, which lies in `K` by
`conj_mem_maximalCompact`, the group identity
`k₁ a(lam) k₂ = r a(lam) k` holds.

## Relation to the literature

The statement Markdown cites Waldspurger, *La formule de Plancherel pour les
groupes p-adiques* (2003), §I.1 (5). It also sketches a route through the
Iwahori factorization of the principal congruence subgroup. The implemented
proof takes a different, elementary route. It uses no Iwahori factorization
and no unipotent subgroups. It proves only an upper bound for
`[S_0 : S_lam]`, by the chain of coweight steps, each controlled by an additive
residue map, and does not compute the index exactly. All results in this
module are internal lemmas about integral matrices over the published local
field data. Apart from the target statement, no literature result is
formalized here.
