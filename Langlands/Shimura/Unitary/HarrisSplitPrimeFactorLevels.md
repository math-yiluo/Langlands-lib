# Harris's levels at a split prime in product form

Author: Worker 19.

This module gives the `p`-adic level subgroups of Harris (1999), (4.1), in
their product form

`K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`,

one compact open subgroup `C_w` of `(K_w ⊗[K] A)ˣ` for every place `w` of the
CM field above the chosen place `𝔭` of the imaginary quadratic field. It
upgrades the decomposition of `HarrisSplitPrimeFactors` to an isomorphism of
topological groups and combines it with the level `K_p = C × ℤ_pˣ` of
`HarrisSplitPrimeLevels`.

## Source

Harris (1999), Section 4, printed p. 309 (PDF p. 11):

"(4.1) `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`. Here `C_v ⊂ (𝒟_1)ˣ` is an open
compact subgroup, which we allow to vary, whereas `C^(j) ⊂ (𝒟_j)ˣ` will be
fixed; we are implicitly identifying (4.2) `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ`".

Harris (1998), Appendix, printed p. 206 (PDF p. 30), (A.2): the `p`-level
`C(N)_p ≅ C_v^{N,0} × ∏_{j>1} C_p^(j) × ℤ_pˣ`.

Here the index `j` is a place `w` of `K` above `𝔭`, `𝒟_j` is `K_w ⊗[K] A`,
and the family `C` assigns `C_w` to every `w`, including the distinguished
place (Harris's `v = v^(1)`); which place is distinguished, and which factors
are fixed or vary, is not encoded.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Generic

- `CompactOpenLevel.pi C`, for a finite family of compact open levels
  `C i` of topological groups `G i`, is the product level of `Π i, G i`
  (`Subgroup.pi`, open by `isOpen_set_pi`, compact by `isCompact_univ_pi`).
  `CompactOpenLevel.mem_pi`: membership is componentwise.
- `linearEquivHomeomorph φ`: a linear isomorphism `φ : M ≃ₗ[S] N` over a
  complete nontrivially normed field `S`, from a module with the `S`-module
  topology onto a finite-dimensional Hausdorff topological vector space, is a
  homeomorphism. The forward map is continuous by
  `IsModuleTopology.continuous_of_linearMap`; for the inverse, `N` carries the
  module topology by Mathlib's `isModuleTopologyOfFiniteDimensional`.

### The Harris setting

As in `HarrisSplitPrimeFactors`: `ι : F →+* K` (so `K` and `A` are
`F`-algebras), a finite place `v` of `ℚ`, a place `𝔭` of `F` above `v` with
bijective completion map `ℚ_v → F_𝔭` (`h𝔭`), and `ℚ_v` an `F`-algebra
through `splitPlaceEmbedding v 𝔭 h𝔭`. Here `A` is finite over `ℚ`, with the
scalar tower `ℚ → K → A`.

- `splitPlaceCoefficient ι v 𝔭 w : ℚ_v →+* K_w` is
  `completionMap 𝔭 w ∘ completionMap v 𝔭`;
  `continuous_splitPlaceCoefficient`: it is continuous.
- `splitPlaceFactorEquiv_smul`: the `w`-component of
  `splitPlaceFactorEquiv` sends `(c s) ⊗ a` to
  `splitPlaceCoefficient c • (component of s ⊗ a)`.
- `splitPlaceComponent ι v 𝔭 h𝔭 w : ℚ_v ⊗[F] A →ₛₗ K_w ⊗[K] A` is the
  `w`-component of `splitPlaceFactorEquiv`, semilinear over
  `splitPlaceCoefficient`.
- `continuous_splitPlaceFactorEquiv`: `splitPlaceFactorEquiv` is continuous
  from the `ℚ_v`-module topology to the product of the `K_w`-module
  topologies; each component is semilinear over a continuous ring
  homomorphism (`IsModuleTopology.continuous_of_linearMapₛₗ`).
- `continuous_splitPlaceFactorEquiv_symm`: its inverse is continuous. With
  `ℚ_v` acting on `K_w ⊗[K] A` through `splitPlaceCoefficient`
  (`Module.compHom`), the product `Π_w K_w ⊗[K] A` is a topological `ℚ_v`-vector
  space (`MulAction.continuousSMul_compHom`), Hausdorff (each factor is
  homeomorphic to a finite power of `K_w` by the published
  `AlgebraInvolution.coordinateEquiv`), and finite-dimensional (it is
  linearly isomorphic to `ℚ_v ⊗[F] A`, and `A` is finite over `F` because it
  is finite over `ℚ`). For the normed field structure of `ℚ_v` given by its
  valuation (`Valued.toNontriviallyNormedField`), `linearEquivHomeomorph`
  applies.
- `splitPlaceUnitsHomeomorph ι v 𝔭 h𝔭 : SplitPrimeUnits A ι v u ≃ₜ*
  Π_{w ∣ 𝔭} FactorUnits K A K_w`, for `u = splitPlaceEmbedding v 𝔭 h𝔭`: the
  units of `splitPlaceFactorEquiv` followed by `MulEquiv.piUnits`, continuous
  in both directions by `Units.continuous_iff` and the two lemmas above.
  `FactorUnits K A K_w` is `(K_w ⊗[K] A)ˣ` with the units topology of the
  `K_w`-module topology (`ImaginaryQuadraticSplitTopology`).
- `splitPlaceUnitsHomeomorph_splitPrimeHomeomorph`: applied to the first
  coordinate of `splitPrimeHomeomorph`, it gives the first coordinate of
  `splitPlacePoints` (by `rfl`).

For `σ : SecondKindInvolution E K A` (with `F` quadratic over `ℚ`):

- `σ.splitPlaceLevel ι v 𝔭 h𝔭 C`, for a family `C w` of compact open levels
  of `FactorUnits K A K_w`, is `σ.splitPrimeLevel ι v u C'` with
  `C' = transport (splitPlaceUnitsHomeomorph …).symm (CompactOpenLevel.pi C)`:
  Harris's level `K_p = Π_w C_w × ℤ_vˣ`.
- `mem_splitPlaceLevel`: a point `g` of `GG(ℚ_v)` lies in it exactly when, for
  every `w`, the `w`-component of `(σ.splitPlacePoints ι v 𝔭 h𝔭 g).1` lies in
  `C w`, and its multiplier lies in `ℤ_vˣ`.
- `splitPlaceLevel_mono`: the level is monotone in `C`.

Global levels `K_p × K^p` and the Harris tower away from `p` at this `K_p` are
obtained by passing `C'` above to `splitPrimeAdelicLevel` and
`harrisSplitPrimeTower` of `HarrisSplitPrimeLevels`.

## Scope

The levels `C_w` are arbitrary compact open subgroups; Harris's principal
congruence subgroup `C_v^{N,0}` (Harris 1998, (A.2)) and the maximal
subgroups `C^(j)` are not constructed, and no maximal order is defined. The
place `𝔭` and the distinguished place among the `w` are inputs.

## Provenance

Derived from Harris (1999), equations (4.1) and (4.2) on printed p. 309, and
Harris (1998), Appendix, (A.1) and (A.2) on printed p. 206, both read in the
original. The use of module topologies, the finite-dimensional comparison of
topologies and the product-of-levels packaging are implementation choices;
`CompactOpenLevel.pi` and `linearEquivHomeomorph` are generic internal
helpers.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Formal dependencies: `Langlands.Shimura.Unitary.HarrisSplitPrimeFactors`
(with `PlaceTensorDecomposition`), `Langlands.Shimura.Unitary.HarrisSplitPrimeLevels`
(with `ImaginaryQuadraticSplitTopology`), the published `Unitary.Adelic`
(`coordinateEquiv`), `PEL.TraceSimilitudesLevels` (`transport`), the published
`Langlands.Global.AdelicFunctoriality` completion maps, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`isModuleTopologyOfFiniteDimensional`, `Valued.toNontriviallyNormedField`,
`IsModuleTopology.continuous_of_linearMapₛₗ`, `MulAction.continuousSMul_compHom`,
`Module.compHom`, `Units.continuous_iff`, `MulEquiv.piUnits`, `Subgroup.pi`,
`isOpen_set_pi` and `isCompact_univ_pi`.
