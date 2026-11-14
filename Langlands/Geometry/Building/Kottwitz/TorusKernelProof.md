# Proof that the torus Iwahori subgroup is the kernel of the torus Kottwitz map

`torusKottwitzKernel : TorusKottwitzKernelStatement.{u}` proves the Library statement
`Langlands.Geometry.Building.Kottwitz.TorusKottwitzKernelStatement`
(`Kottwitz/TorusKernelStatement`). This is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (Cambridge, 2023), Proposition 11.1.5, `T(K)^0 = ker(κ_T)`, printed p. 423,
PDF p. 454. The proof has no premises and uses only published Library results together
with the helper lemmas of this file.

Notation: `K = UnramifiedClosure F` and `F^sep = SeparableClosure F`. The torus `T` is
defined over `k`, where `k → K → F^sep` is a scalar tower and `K/k` is normal. Write `L`
for a finite Galois extension of `K` inside `F^sep`. `T_K` is the commutative base change
of `T` to `K`, and `(T_K)_L` is its base change to `L`. `T_L = baseChanged k L T` is the
direct base change from `k` to `L`. `T(L)` denotes the `L`-coefficient points
`affinePoints T.toGrp (CommAlgCat.of k L)` of the original group scheme, and
`N : T(L) → T(K)` is the relative norm `GaloisPoint.relativeNorm k K L T`. Finally,
`κ = torusKottwitz F k T hT`.

## Main theorem

Fix `F`, `k`, `T`, `hT`, `L` and the splitting hypothesis `hsplit` for `(T_K)_L`. Use the
affineness instance `torusIsAffine k T hT`, as `TorusKottwitzExistenceStatement` does.

1. **Splitting of `T_L`.** The tower comparison
   `towerBaseChangeIso k K L T.toGrp : (T_K)_L ≅ T_L` and `IsSplitTorus.of_iso` turn
   `hsplit` into `hL : IsSplitTorus T_L`.
2. **The norm square.** `torusKottwitzExistence` (the published proof of KP
   Proposition 11.1.1 in `Kottwitz/TorusMapProof`) shows that the selected map `κ`
   satisfies `IsTorusKottwitzHom`. In particular it satisfies the norm square
   `TorusNormLawAt F k T L hL κ` at `L`.
3. **Kernel identity.** `torusNormIwahori_eq_comap_ker` proves the equality of subgroups
   for every homomorphism satisfying the norm square at `L`. Applying it to `κ` gives the
   statement.

## The kernel of a map satisfying the norm square

The rest of the file works on the coefficient points `T(L)`.

**Split valuation on `T(L)`.** `coeffSplitValuation F k T L hL : T(L) →* X_*(T_L)` is
`splitValuation T_L hL (normalizedIntermediateValuation F L)` composed with the inverse of
`baseChangeCoeffEquiv k L T.toGrp`. By `normLawValue_eq_coeffSplitValuation` (which holds
by `rfl`), the value of the norm square at `x ∈ T(L)` is the inertia-coinvariant class of
`extendGeometricCocharacters k L F^sep T (coeffSplitValuation x)`.

**`eq_one_iff_exists_coeffSplitValuation`.** If `κ` satisfies the norm square at `L`, then
for `t ∈ T(K)`,

```
κ t = 1  ↔  ∃ y ∈ T(L), coeffSplitValuation y = 1 ∧ N y = t.
```

* Backward: by `torusNormLawAt_iff`, `κ (N y)` is the class of the extended split
  valuation of `y`. That class is `0` when the split valuation is trivial.
* Forward: the norm is onto (`relativeNorm_unramifiedClosure_surjective`), so `t = N x`.
  Then `κ t = 1` says that the extended split valuation of `x` lies in the augmentation
  submodule `Representation.Coinvariants.ker` of the inertia action
  (`Representation.Coinvariants.mk_eq_zero`). `exists_relativeNorm_eq_one_of_mem_ker`
  gives `z` with `N z = 1` and the same extended split valuation. Extension of
  cocharacters is injective (`extendGeometricCocharacters_bijective`), so `z` and `x`
  have the same split valuation. Take `y = x z⁻¹`
  (`exists_relativeNorm_eq_one_of_normLawValue_eq_zero`).

**`exists_relativeNorm_eq_one_of_mem_ker`.** Every element `w` of the inertia augmentation
submodule is the extended split valuation of a point of norm one. The proof is by
`Submodule.span_induction`. Zero, sums and integer multiples are handled by the identity
point, products and integer powers, since `N` and the split valuation are homomorphisms.
A generator has the form `ρ(g) v - v`, where `g` is an automorphism of `F^sep` over `k`
that is trivial on `K` (`relativeInertia`) and `v` is a geometric cocharacter.

* `v` is the extension of some `c₀ ∈ X_*(T_L)`, by `extendGeometricCocharacters_bijective`.
* `g` is trivial on `K`, so it is a `K`-automorphism. Its restriction to the normal
  extension `L` is some `τ ∈ Gal(L/K)` compatible with `g`
  (`exists_restrict_of_mem_relativeInertia`).
* `exists_relativeNorm_eq_one_galois_sub` gives `z` with `N z = 1` and split valuation
  `τ c₀ - c₀`. By `extendGeometricCocharacters_galois`, this extends to `ρ(g) v - v`.

**`exists_relativeNorm_eq_one_galois_sub`.** This is KP's uniformizer step.

1. Choose `a ∈ L^×` whose normalized valuation is `1` (`exists_orderUnits_eq_one`).
2. Let `y = c₀(a)`, the evaluation `coefficientEvaluation k L T (a ⊗ c₀)`. Then
   `coeffSplitValuation y = c₀` by `coeffSplitValuation_tmul_of_order_eq_one`. That lemma
   comes from `coefficientEvaluation_tmul_eq` and `splitValuation_cocharacterPoints`.
3. By `coefficientEvaluation_galois_tmul`, the conjugate `τ(y)` is `(τ c₀)(τ a)`. The unit
   `τ a` again has normalized valuation `1` (`orderUnits_algEquiv`), so
   `coeffSplitValuation τ(y) = τ c₀`.
4. Take `z = τ(y) / y`. Then `N z = 1`, because the norm is invariant under `Gal(L/K)`
   (`relativeNorm_relativeConjugate`, proved here by reindexing the product in
   `relativeExtend_norm`). Its split valuation is `τ c₀ - c₀` (`map_div`, `ofAdd_sub`).

## Comparison of the bounded subgroups

`mem_characterValuationKernel_iff_splitValuation_eq_one` covers the split torus `T_L`. A
rational point lies in `characterValuationKernel (intermediateValuation F L)`, the
bounded subgroup for the spectral valuation, iff its split valuation for
`normalizedIntermediateValuation F L` is trivial.

* Forward: `splitValuation_eq_one_of_mem`, using that the normalized valuation is
  equivalent to the spectral one (`normalizedIntermediateValuation_spec'`).
* Backward: `splitValuation_pairing` shows that every rational character has normalized
  order `0` at the point. The same equivalence turns this into spectral valuation one.

This is how the proof relates the two valuation conventions that the statement keeps
apart.

## Transport along the tower comparison

The statement's left side lives on `(T_K)_L` and its norm `rationalNorm K L T_K`. The norm
square lives on `T_L` and `N`. The file compares them through
`towerBaseChangeIso k K L T.toGrp`:

* `relativeNorm_towerBaseChangeIso`: for `x ∈ (T_K)_L(L)`, the relative norm of the
  transported point is the `K`-coefficient projection of `rationalNorm K L T_K x`. It
  follows from `relativeRationalNorm_towerBaseChangeIso` and
  `baseChangeCoeffEquiv_relativeRationalNorm`. `relativeNorm_towerBaseChangeIso_inv` is
  the same identity for the inverse transport. It uses `rationalPoints_map_hom_map_inv`,
  which says that the point maps of an isomorphism and its inverse cancel.
* `coeffSplitValuation_towerBaseChangeIso_eq_one` and
  `towerBaseChangeIso_inv_mem_characterValuationKernel`: both directions of the tower
  comparison preserve the bounded subgroups. Each direction is
  `map_characterValuationKernel_le` (`KPZeroNormKernel`) combined with the comparison of
  the previous section. The lemma `mem_characterValuationKernel_of_mem_baseChanged` holds
  by definitional unfolding. It identifies the bounded subgroup of the iterated base
  change of `T.toGrp` with that of the iterated commutative base change of `T`.

**`torusNormIwahori_eq_comap_ker`.** By `mem_torusNormIwahori`, `t ∈ T_K(K)` lies in the
norm subgroup iff `t = rationalNorm K L T_K x` for some bounded `x`. The other side is
`κ (baseChangeCoeffEquiv k K T.toGrp t) = 1`, which `eq_one_iff_exists_coeffSplitValuation`
rewrites. Given `x`, the transported point `y` has trivial split valuation, and `N y` is
the projection of `t`. Conversely, given `y`, its inverse transport `x` is bounded, and
`rationalNorm x = t` follows from `relativeNorm_towerBaseChangeIso_inv` and the injectivity
of `baseChangeCoeffEquiv`.

## Relation to KP's proof

KP's proof uses three facts: the norm `T(L) → T(K)` is surjective, the norm square gives
`T(K)^0 ⊆ ker(κ_T)`, and the converse comes from writing an element of the inertia
augmentation as a sum of `y - σ y` realized by norm-one points `y(ϖ)/σ(y(ϖ))`. The Lean
proof follows this route. Here `ϖ` is a unit of normalized valuation one, and the
norm-one points are `τ(y(ϖ))/y(ϖ)` (the inverse of KP's quotient, so the sign of the
difference is reversed). The proof does not use independence of `T(K)^0` from the
splitting field (KP Lemma 2.5.12). The equality is proved separately for every finite
Galois splitting field `L`.

## Implementation notes

Several transport steps are written as explicit term proofs (`Eq.trans` and `congrArg`)
rather than `rw` chains. The rewriting versions caused elaborator and kernel heartbeat
timeouts, because the two presentations of the base-changed group schemes are only
definitionally equal. No heartbeat options are raised. The file sets
`backward.isDefEq.respectTransparency false`, as many of the surrounding Kottwitz modules
do.
