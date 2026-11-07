# Transport of ramification groups along field isomorphisms

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.TransportProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.InertiaProof`, which brings in the earlier
Herbrand modules.

## What the module proves

### Isomorphic fields

Let `p` be a prime and let `L₁`, `L₂` be finite p-adic fields with arbitrary local-field
realizations `T₁ : L₁.TopologicalData` and `T₂ : L₂.TopologicalData`. Let `K` be a field with
`Padic p`-algebra structure, below both, with scalar towers `Padic p → K → Lᵢ`. Let
`f : L₁.Carrier ≃ₐ[K] L₂.Carrier`. Conjugation by `f` is `f.autCongr`, which sends `σ` to
`f ∘ σ ∘ f⁻¹`. The module proves:

- `map_mem_integers_iff T₁ T₂ K f x`: `f x ∈ T₂.Integers` if and only if `x ∈ T₁.Integers`.
- `integerEquiv T₁ T₂ K f : T₁.Integers ≃+* T₂.Integers`, the restriction of `f`. This is a
  named definition.
- `integerEquiv_smul`: for `σ` in `L₁.Carrier ≃ₐ[K] L₁.Carrier`, `integerEquiv` carries the
  action of `σ` (`Padic.integerAction T₁ K`) to the action of `f.autCongr σ`
  (`Padic.integerAction T₂ K`).
- `autCongr_mem_lowerRamificationGroup_iff`: `f.autCongr σ` lies in the lower group
  `Padic.lowerRamificationGroup T₂ K i` if and only if `σ` lies in
  `Padic.lowerRamificationGroup T₁ K i`, for every `i : ℕ`.
- `autCongr_mem_lowerRamificationGroupInt_iff`: the same for the integer-indexed groups
  `Padic.lowerRamificationGroupInt`.
- `lowerGroupOrder_eq_of_algEquiv`: the lower group orders `Padic.lowerGroupOrder` agree.
- `herbrandPhi_eq_of_algEquiv`, `herbrandPsi_eq_of_algEquiv`: so do `Padic.herbrandPhi` and
  `Padic.herbrandPsi`, at every real argument.
- `autCongr_mem_upperRamificationGroup_iff` and `map_autCongr_upperRamificationGroup`: for every
  real `v`, conjugation by `f` maps `Padic.upperRamificationGroup T₁ K v` onto
  `Padic.upperRamificationGroup T₂ K v`.
- `upperRamificationGroup_eq_of_realization T T' K v`: the case `f = id`. Two realizations `T`
  and `T'` of the same field give the same upper groups.

### Algebraic extensions of the base

Let `K : PadicField p` and let `Ω₁`, `Ω₂` be fields that are `K.Carrier`-algebras and
`Padic p`-algebras, with scalar towers `Padic p → K.Carrier → Ωᵢ`.

- `upperGroupIn K Ω₁ v` is a named definition: a subgroup of `Gal(Ω₁/K.Carrier)`. It is the
  intersection, over all `M : FiniteGaloisIntermediateField K.Carrier Ω₁`, of the preimages
  under `AlgEquiv.restrictNormalHom M` of
  `canonicalUpperRamificationGroup (finiteGaloisPadicField K M) K.Carrier v`.
  `mem_upperGroupIn_iff` unfolds this intersection.
- `absoluteUpperRamificationGroup_eq_upperGroupIn K v`: for `Ω₁ = AlgebraicClosure K.Carrier`
  it is the Library group `absoluteUpperRamificationGroup K v` (by `rfl`).
- `comapFiniteGalois K e M`, a named definition. For `e : Ω₁ ≃ₐ[K.Carrier] Ω₂` and a finite
  Galois subfield `M` of `Ω₂`, it is the image of `M` under `e.symm`, as a finite Galois
  subfield of `Ω₁`. The named definition `comapFiniteGaloisEquiv K e M` is the induced
  isomorphism onto `M`. By `comapFiniteGaloisEquiv_coe`, it is `e` on elements.
- `autCongr_restrictNormalHom`: restricting `τ` to `comapFiniteGalois K e M` and conjugating
  by `comapFiniteGaloisEquiv K e M` gives the restriction of `e.autCongr τ` to `M`.
- `autCongr_mem_upperGroupIn_iff K e v τ`: `e.autCongr τ ∈ upperGroupIn K Ω₂ v` if and only if
  `τ ∈ upperGroupIn K Ω₁ v`. So the absolute upper filtration can be computed in any algebraic
  closure of the base, and conjugation by a `K.Carrier`-isomorphism matches the two answers.
  `autCongr_mem_upperGroupIn_of_mem` is the forward implication.

## Sources

There is no new mathematical content from the literature. These are naturality statements for
Serre's ramification groups and Herbrand functions, *Local Fields*, Chapter IV, §§1 and 3
(registered as `serre-1979-local-fields`). The ramification groups and the functions `φ` and
`ψ` are defined from the valuation ring alone, so a field isomorphism preserves all of them.
All declarations are internal steps toward comparing absolute upper groups of a finite
extension inside one fixed algebraic closure.

## Proof (as implemented)

1. **Integers.** By `isIntegral_iff_mem_integers`, for any realization the integer ring is
   the set of elements integral over the p-adic integers `(ValuativeRel.valuation (Padic p)).integer`.
   The integers act through `Algebra.compHom` and `Padic p`. Since `f` is `K`-linear, it is
   `Padic p`-linear (`AlgEquiv.restrictScalars`). So it is an injective algebra map over the
   p-adic integers, and `isIntegral_algHom_iff` transfers integrality. This gives
   `map_mem_integers_iff` and the ring isomorphism `integerEquiv`.
2. **Equivariance.** For `a` in `T₁.Integers`, `f (σ a) = (f ∘ σ ∘ f⁻¹) (f a)`.
3. **Lower groups and their orders.** These are the `QuotientProof` lemmas
   `mem_lowerRamificationGroup_iff_of_equivariant` and `lowerRamificationCard_of_equivariant`,
   applied to `integerEquiv` and `f.autCongr`. The integer-indexed groups are `⊤` at negative
   indices and the natural lower groups otherwise.
4. **Herbrand functions.** For `u ≤ 0` both functions are the identity
   (`Padic.herbrandPhi_of_nonpos`). For `u ≥ 0`, `Padic.herbrandPhi_floor` expresses `φ` through
   the lower group orders, which agree by step 3. `ψ` is the inverse of the strictly increasing
   `φ`, so it agrees too.
5. **Upper groups.** `Padic.upperRamificationGroup T K v` is the integer lower group of index
   `⌈ψ(v)⌉` (`upperRamificationGroup_eq_lower`). Steps 3 and 4 then give the correspondence.
   Surjectivity of `f.autCongr` gives the image form. For the realization corollary, take
   `f = AlgEquiv.refl`, whose `autCongr` is the identity (`AlgEquiv.autCongr_refl`).
6. **Change of extension.** `comapFiniteGalois` is finite-dimensional and Galois, being
   isomorphic to `M` (`IntermediateField.equivMap`, `IsGalois.of_algEquiv`). The commutation
   `autCongr_restrictNormalHom` is checked on elements:
   - `AlgEquiv.restrictNormalHom_apply` reads restrictions in `Ω₁` and `Ω₂`;
   - `comapFiniteGaloisEquiv_coe` reads the isomorphism as `e`;
   - both sides become `e (τ z)`.

   For `τ` in `upperGroupIn K Ω₁ v` and a finite Galois `M` in `Ω₂`, step 5 for
   `comapFiniteGaloisEquiv K e M` moves the upper-group condition on `comapFiniteGalois K e M`
   to `M`. This gives the forward implication. The converse applies it to `e.symm` and uses
   `e.symm.autCongr (e.autCongr τ) = τ` (`AlgEquiv.autCongr_symm`).

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
