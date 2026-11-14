# Proof of existence, uniqueness and splitting-field independence of the torus Kottwitz map

`torusKottwitzExistence : TorusKottwitzExistenceStatement.{u}` proves the Library statement
`Langlands.Geometry.Building.Kottwitz.TorusKottwitzExistenceStatement`
(`Kottwitz/TorusMapStatement`). This is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, Proposition 11.1.1 (printed pp. 421–422, PDF pp. 452–453), minus its
Galois-equivariance clause, which belongs to `TorusKottwitzDescentStatement`.

Notation: `K = UnramifiedClosure F` and `F^sep = SeparableClosure F`. The coefficient field
`k` sits in the normal scalar tower `k → K → F^sep`, and `T` is a torus over `k`. A finite
Galois splitting field means an intermediate field `L` of `F^sep / K` that is finite Galois
over `K` and over which `T` splits.

## Proof

Fix `F`, `k`, `T` and `hT : IsTorus T.toGrp`, and use the affineness instance
`torusIsAffine k T hT`, as the statement does.

1. **A splitting field.** `exists_finiteGalois_splitting` (TorusSplittingField) gives a
   finite Galois splitting field `L₀`.
2. **Existence at `L₀`.** `exists_torusNormLawAt` (TorusKottwitzLaw) gives
   `κ₀ : T(K) →* X_*(T)_I` with `TorusNormLawAt` at `L₀`. It descends the top-right
   composite of KP's square along the surjective norm `T(L₀) → T(K)`.
3. **Independence of the splitting field.** `torusNormLawAt_of_torusNormLawAt`
   (TorusKottwitzTransfer) moves the norm square from `L₀` to any finite Galois splitting
   field `L`, so `κ₀` satisfies `IsTorusKottwitzHom`. This is KP's step "if `κ_T` makes the
   diagram commute for one `L`, it does so for every `L`". KP compare `L₁ ⊆ L₂` using that
   `L₂/L₁` is totally ramified. The Lean proof makes the same comparison inside the
   compositum, using the norm compatibility of the normalized valuations
   (`normalizedIntermediateValuation_norm`, TorusNormValuation).
4. **The selected map.** Since a homomorphism with the property exists, `torusKottwitz_spec`
   shows that the epsilon-chosen `torusKottwitz F k T hT` satisfies `IsTorusKottwitzHom`.
5. **Uniqueness.** `eq_of_torusNormLawAt` at `L₀` shows that any `κ` with
   `IsTorusKottwitzHom` equals `κ₀`, because the norm `T(L₀) → T(K)` is onto. This gives
   `∃! κ, IsTorusKottwitzHom F k T κ` and `torusKottwitz F k T hT = κ₀`.
6. **Surjectivity of the map.** `surjective_of_torusNormLawAt` at `L₀`, applied to the
   selected map.
7. **The per-field clauses.** For every finite Galois splitting field `L`:
   - the norm `T(L) → T(K)` is onto (`relativeNorm_unramifiedClosure_surjective`, from
     the vanishing of Tate cohomology over the dimension-`≤ 1` field `K`);
   - `TorusNormLawAt F k T L hL κ ↔ κ = torusKottwitz F k T hT`. Forward, both `κ` and the
     selected map satisfy the square at `L`, so `eq_of_torusNormLawAt` at `L` makes them
     equal. Backward, the selected map satisfies the square at every `L` by step 4.

## Helper modules

The proof uses these helper modules, all in `Langlands/Geometry/Building/Kottwitz/`:

- `TorusNormCohomology`: Tate cohomology of `T(L)` for split `T_L`, surjectivity of the
  norm, the kernel of the norm, and transitivity of norms.
- `TorusNormValuation`: `K` has dimension `≤ 1`; the normalized valuations of finite
  extensions of `K` exist, are Galois invariant and are compatible with norms. This also
  proves `NormalizedIntermediateValuationStatement`.
- `TorusSplittingField`: existence of a finite Galois splitting field inside `F^sep`.
- `TorusCocharacterTower`: evaluations `ν(u)` of cocharacters at units, and their
  behaviour under extension, Galois action and norm.
- `TorusKottwitzLaw`: the norm square at one field. It gives existence, uniqueness and
  surjectivity at one `L`.
- `TorusKottwitzTransfer`: independence of the splitting field.
