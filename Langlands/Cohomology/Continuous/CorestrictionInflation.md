# Ordinary corestriction and maps along compatible surjections

Author: Worker 222.

This module proves one general compatibility of the Library's ordinary
corestriction `Tate.ordinaryCohomologyCorestriction` with Mathlib's
`groupCohomology.map`. The refinement proof
`Langlands.Continuous.finiteCorestrictionRefinement` uses it. Every other
declaration in the module is an auxiliary step of its proof.

## Main theorem

`Langlands.Continuous.ordinaryCohomologyCorestriction_comp_map` takes the
following data, in an arbitrary common universe `u`:

- a commutative ring `R` and groups `Γ`, `Δ`;
- a surjective homomorphism `π : Γ →* Δ`;
- a subgroup `K` of `Δ` and a subgroup `K'` of `Γ`, each with a `Fintype`
  instance on its coset space. The hypothesis `hK : ∀ g, g ∈ K' ↔ π g ∈ K`
  says that `K'` is the preimage of `K`;
- a homomorphism `π' : K' →* K` with `hπ' : ∀ g, (π' g : Δ) = π g`, so `π'` is
  the restriction of `π`;
- `A : Rep R Δ`, `B : Rep R Γ`, and a morphism `φ : Rep.res π A ⟶ B`;
- a morphism
  `φ' : Rep.res π' (Rep.res K.subtype A) ⟶ Rep.res K'.subtype B` with the same
  underlying linear map as `φ` (`hφ'`);
- a degree `q : ℕ`, including `q = 0`.

It states

```
Tate.ordinaryCohomologyCorestriction K A q ≫ groupCohomology.map π φ q =
  groupCohomology.map π' φ' q ≫ Tate.ordinaryCohomologyCorestriction K' B q.
```

The two `Fintype` instances are arbitrary. Under `hK` and the surjectivity of
`π`, the map `Γ ⧸ K' → Δ ⧸ K` induced by `π` is a bijection. The proof uses
this bijection only through `sum_quotient_out_map` below.

The two sides are not equal on cochains. Each corestriction uses
`Quotient.out` representatives and the coset coordinate
`Tate.cosetCoordinate K δ = δ * (QuotientGroup.mk δ⁻¹ : Δ ⧸ K).out`, an
element of `K`. The representatives of
`Γ ⧸ K'` need not map to the chosen representatives of `Δ ⧸ K`. The proof
therefore builds an explicit cochain homotopy.

## Proof

Write `T_K A` for `Tate.homogeneousCochainTransfer K A`, and `c_X` for
`Tate.cochainsIsoStandard X`. `Tate.ordinaryCorestrictionCochainMap K A` is
`c_{res A}.hom ≫ T_K A ≫ c_A.inv`.

### Prism operator on homogeneous chains (section `Prism`)

The chains are the free modules `MonoidAlgebra R (Fin m → X)` on tuples, with
the homogeneous differential `Rep.standardComplex.d`.

- `chainCone x m` prepends the coordinate `x` to every tuple. The cone
  identity `standard_d_chainCone` is `d (cone_x y) = y - cone_x (d y)` for
  chains `y` of positive length.
- Given maps `α β : X → Y`, `chainPrism α β m` sends chains of length `m` to
  chains of length `m + 1`. It is zero for `m = 0`. On a generator `d` of length
  `m + 1` it is defined recursively as
  `[β(d₀), α(d₀), …, α(d_m)] - cone_{β(d₀)} (chainPrism (tail d))`
  (`chainPrism_succ_single`).
- `chainPrism_identity_single` proves the prism identity on generators:
  `d (P d) + P (d d) = (α ∘ d) - (β ∘ d)`. The proof is by induction on the
  length and uses the cone identity.
- `chainPrism_mapDomain` shows that `P` commutes with coordinatewise maps
  `σ`, `τ` whenever `α ∘ σ = τ ∘ α` and `β ∘ σ = τ ∘ β`.

### Coordinatewise maps of diagonal representations (section `Coordinates`)

Let `ι : H →* G₁`, `ψ : H →* G₂`, and `θ : G₁ → G₂` with
`θ (ι h * g) = ψ h * θ g`.

- `coordinateHom ι ψ θ` is the map
  `Rep.res ι (Rep.diagonal R G₁ m) ⟶ Rep.res ψ (Rep.diagonal R G₂ m)` that
  applies `θ` to every coordinate. Equivariance follows from the hypothesis on
  `θ`, and `diagonal_ρ_eq` writes the diagonal action as a coordinatewise map.
- `prismHom ι ψ α β` is `chainPrism α β` as a morphism of the same kind,
  raising the length by one. Its equivariance is `chainPrism_mapDomain`.
- `coordinateHom_sub_zero` and `coordinateHom_sub_succ` restate the prism
  identity for these morphisms and the differentials of
  `Rep.standardComplex`. In degree zero
  `θ_α - θ_β = prismHom ≫ res d`. In positive degree
  `θ_α - θ_β = prismHom ≫ res d + res d ≫ prismHom`.

### Traces of comparisons (section `Transfer`)

For `Φ : Rep.res K'.subtype P ⟶ Rep.res π' Q`, the linear map
`comparisonTransfer φ' Φ` sends `F : Q ⟶ Rep.res K.subtype A` to
`Tate.homTransfer K' P B (Φ ≫ (Rep.resFunctor π').map F ≫ φ')`. It is
additive in `Φ` (`comparisonTransfer_sub`, `comparisonTransfer_add`). It moves
a differential of `Q` onto `F` (`comparisonTransfer_comp_map`). It turns
precomposition of `Φ` with a restricted map `d` into precomposition of the
result with `d` (`comparisonTransfer_map_comp`, from `Tate.homTransfer_precomp`).

### Cochain maps on the standard Hom complexes (section `CochainMaps`)

For `f : G₂ →* G₁`, `standardMap f m` is `coordinateHom` for `f` itself.
The imported `Tate.cochainsIsoStandard_hom_single` and
`Tate.cochainsIsoStandard_inv_apply` from `CohomologyTransferZero` evaluate
the standard cochain isomorphism on homogeneous generators and on
partial-product tuples. `cochainsIsoStandard_cochainsMap` proves that Mathlib's
inhomogeneous cochain map `groupCohomology.cochainsMap f ψ`, transported by
`c_X` and `c_Y`, sends `F` to `standardMap f (n + 1) ≫ res_f F ≫ ψ` in degree
`n`.

### Change of representatives (section `Choice`)

`sum_quotient_out_map` assumes `hπ` and `hK`. It proves, for every
`f : Δ → M` with `f (δ * k) = f δ` for `k ∈ K`, that
`∑ p : Γ ⧸ K', f (π p.out) = ∑ q : Δ ⧸ K, f q.out`. The proof applies
`Fintype.sum_bijective` to `p ↦ [π p.out]`.

### The homotopy (section `Comparison`)

Two coset coordinates `Γ → K` enter:

- `α g = Tate.cosetCoordinate K (π g)`;
- `β g = π' (Tate.cosetCoordinate K' g)`.

Both satisfy `θ (k' * g) = π' k' * θ g` for `k' ∈ K'` (`imageCoordinate_mul`
and `mapCoordinate_mul`).

`leftComposite` is `T_K A ≫ c_A.inv ≫ cochainsMap π φ ≫ c_B.hom`.
`rightComposite` is
`c_{res A}.inv ≫ cochainsMap π' φ' ≫ c_{res B}.hom ≫ T_{K'} B`. Both are maps
of the standard Hom complexes from `K`-cochains of `Rep.res K.subtype A` to
`Γ`-cochains of `B`. In degree `n`:

- `rightComposite_f_apply`: `rightComposite` sends `F` to
  `comparisonTransfer φ' (coordinateHom β (n + 1)) F`. This uses
  `cochainsIsoStandard_cochainsMap` and
  `standardCosetComparison_comp_standardMap`. The latter states that the
  standard coset comparison for `K'` followed by `standardMap π'` is
  `coordinateHom β`.
- `leftComposite_f_apply`: `leftComposite` sends `F` to
  `comparisonTransfer φ' (coordinateHom α (n + 1)) F`. After
  `cochainsIsoStandard_cochainsMap` and `Tate.homTransfer_apply`, both sides
  are sums over coset representatives. The `Δ ⧸ K` sum becomes the `Γ ⧸ K'`
  sum by `sum_quotient_out_map`; its summand is right `K`-invariant by
  `Tate.cosetCoordinate_subgroup_mul` and the equivariance of `F`. The summands
  then agree by the equivariance of `φ` and by `hφ'`.

`prismHomotopy` has component
`comparisonTransfer φ' (prismHom α β (j + 1))` from degree `j + 1` to degree
`j`. `leftComposite_sub_rightComposite` proves

```
leftComposite - rightComposite = Homotopy.nullHomotopicMap' prismHomotopy.
```

In each degree it combines the two formulas above with
`comparisonTransfer_sub`, the Rep-level prism identities, and the compatibility
of `comparisonTransfer` with differentials.

### Conclusion

By `Homotopy.equivSubZero`, `Homotopy.ofEq`, and `Homotopy.nullHomotopy'`, the
two composites are homotopic. Cancelling `c_B.hom ≫ c_B.inv` and
`c_{res A}.hom ≫ c_{res A}.inv` gives

```
ordinaryCorestrictionCochainMap K A ≫ cochainsMap π φ
  = c_{res A}.hom ≫ leftComposite ≫ c_B.inv,
cochainsMap π' φ' ≫ ordinaryCorestrictionCochainMap K' B
  = c_{res A}.hom ≫ rightComposite ≫ c_B.inv.
```

Both sides of the theorem are composites of `HomologicalComplex.homologyMap`s.
`HomologicalComplex.homologyMap_comp` merges each side into one homology map,
and `Homotopy.homologyMap_eq` for the conjugated homotopy proves them equal.

## Provenance

The theorem is internal. It was introduced for the refinement compatibility of
finite-stage corestriction (task `70dc4748-9aa1-4c8c-8f94-5de992926c61`). It is
the expected fact that corestriction commutes with maps along a compatible pair
`(π, φ)` when `π` induces a bijection of coset spaces. Its statement and proof
were written directly for the Library's definitions. They follow no cited
source. The prism operator is the usual simplicial prism for the two
coordinatewise maps `α` and `β`, built here by the recursive cone formula.

The module uses `set_option backward.isDefEq.respectTransparency false`
throughout, as the imported `Langlands.Cohomology.Tate.CohomologyTransfer`
does. No hypothesis beyond those listed above is assumed. The proof uses only
the axioms `propext`, `Classical.choice`, and `Quot.sound`. Pinned environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
