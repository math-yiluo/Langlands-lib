# Harris's levels `K(N, m)` through an identification of `GG` and `GJ` away from `p`

Author: Worker 19.

Harris (1999), Section 4, works with two unitary similitude groups, `GG` and
`GJ`, attached to two algebras `ℬ` and `𝒟` with involutions of the second
kind that are isomorphic away from the distinguished place, the real place
`σ₁` and their complex conjugates. Levels of `GJ(A_f^p)` are transported to
`GG(A_f^p)` "via an identification `GG(A_f^p) ≅ GJ(A_f^p)`", and combined
with the `p`-level to form `K(N, m)`. This module makes the identification a
topological isomorphism induced by an isomorphism of algebras with
involution over the prime-to-`p` finite adeles, defines `K(N, m)`, and
reindexes the Harris tower by the levels of `GJ(A_f^p)`.

## Source

Harris (1999), Section 4, printed p. 308 (PDF p. 10): "We fix a prime
`v = v^(1) ∈ S(ℬ)` of residue characteristic `p`, and assume
`inv_v(ℬ) = 1/n`. Moreover, we assume `𝒟` and `ℬ` are isomorphic away from
`v`, `σ₁`, and their complex conjugates."

Printed p. 309 (PDF p. 11): "Let `K(m) = K' × K_ℓ(m) ⊂ GJ(A_f)` be one of the
level subgroups chosen above. Assume `K' = K'^{,p} × K_p` and write
`K(m)^p = K'^{,p} × K_ℓ(m)` … Finally, fix a positive integer `N` and define
an open compact subgroup `K(N, m) = K(N)_p × K(m)^p ⊂ GG(A_f)`, where
`K(m)^p` is defined as above via an identification `GG(A_f^p) ≅ GJ(A_f^p)`".
Proposition 4.4 then lets `K(N, m)^p` vary, with `GG(A_f^p)`-equivariance.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Points of isomorphic algebras with involution

In namespace `AlgebraInvolution`, for `σ : AlgebraInvolution ℚ A`,
`τ : AlgebraInvolution ℚ B`, a commutative topological `ℚ`-algebra `S`, an
`S`-algebra isomorphism `e : S ⊗[ℚ] A ≃ₐ[S] S ⊗[ℚ] B` and
`he : ∀ x, e (σ_S x) = τ_S (e x)` (with `σ_S = σ.baseChange S`):

- `pointsHomeomorphOfEquiv σ τ e he : σ.Points S ≃ₜ* τ.Points S` is the
  published `similitudesEquiv` of the scalar-extended involutions (a point
  `(g, c)` goes to `(e g, c)`), with continuity in both directions: `e` and
  `e.symm` are `S`-linear between modules with the `S`-module topology
  (`IsModuleTopology.continuous_of_linearMap`), hence continuous on units
  (`Continuous.units_map`), and the multiplier is unchanged.
- `pointsHomeomorphOfEquiv_unit` and `pointsHomeomorphOfEquiv_multiplier`
  record these formulas.

### Harris's two inner forms

`E`, `K`, `F` are as in the published Harris setting; `B` and `D` are
`K`-algebras with `σB : SecondKindInvolution E K B` (for `GG`) and
`σD : SecondKindInvolution E K D` (for `GJ`); `p` is a natural number.

- `σB.innerFormPrimeToEquiv σD p e he : GJ(A_f^p) ≃ₜ* GG(A_f^p)`, for an
  isomorphism `e : A_f^p ⊗[ℚ] D ≃ₐ A_f^p ⊗[ℚ] B` over the published
  prime-to-`p` finite adeles `PrimeToFiniteAdeles p` intertwining the
  scalar-extended rational involutions, is `pointsHomeomorphOfEquiv`. Here
  `GG(A_f^p)` and `GJ(A_f^p)` are the published `PrimeToPoints p`.

Assume `B` finite over `ℚ`, `p` prime, `v` the place above `p`, `ι : F →+* K`
and `u : F →+* ℚ_v`.

- `σB.innerFormAdelicLevel σD p ι hp v u C e he Km` is Harris's
  `K(N, m) = K_p × K(m)^p ⊂ GG(A_f)`: the published
  `splitPrimeAdelicLevel` of `σB` for the split-prime level
  `K_p = C × ℤ_vˣ` (`C` a compact open subgroup of `(ℚ_v ⊗[F, u] B)ˣ`) and the
  level `transport θ Km` of `GG(A_f^p)`, where `Km` is a level `K(m)^p` of
  `GJ(A_f^p)` and `θ = innerFormPrimeToEquiv`.
- `mem_innerFormAdelicLevel`: `g ∈ K(N, m)` exactly when its local image at
  `v` lies in `K_p` and `θ⁻¹` of its prime-to-`p` component lies in `K(m)^p`.

For `DB : CentralSimpleUnitaryData E K B n` with the Harris signature
hypothesis `h` (and `ℚ → K → B` a scalar tower), `τ₀ : F →+* ℂ`, `C`, `e` and
`he` as above:

- `harrisInnerFormTower σD p ι hp v u DB h τ₀ C e he :
  CompactOpenLevel (GJ(A_f^p)) ⥤ TopCat` is the published
  `transportFunctor θ` followed by the published `harrisSplitPrimeTower` at
  `K_p`: the level spaces of the Harris tower over the levels `K(N, m)`,
  indexed by `K(m)^p`.
- `innerForm_awayOver_obj`: the away functor at `K_p`, after
  `transportFunctor θ`, sends `K(m)^p` to `innerFormAdelicLevel` (by `rfl`).
- `harrisInnerFormTowerIso`: the Harris level tower
  `harrisUnitaryLevelTower DB h ι τ₀` at the levels `K(N, m)`, as `K(m)^p`
  varies, is naturally isomorphic to `harrisInnerFormTower` (whiskering of the
  published `harrisSplitPrimeTowerIso`).

## Scope

The identification is constructed from given data `e`; its existence, which
follows in Harris's setting from the local isomorphisms of `𝒟` and `ℬ` away
from `v`, `σ₁` and their conjugates, is not proved, and no local-global
patching is done. `GJ` is used only through its prime-to-`p` points; its
definite signature, its levels at `p` and `ℓ`, and the automorphic forms of
Section 3 are not treated here. The `p`-level is the arbitrary-`C` level
`K_p = C × ℤ_vˣ`; Harris's `K(N)_p` with the congruence subgroup
`C_v^{N,0}` is not constructed (the product form over places is in
`HarrisSplitPrimeFactorLevels`).

## Provenance

Derived from Harris (1999), Section 4, printed pp. 308-309: the assumption
that `𝒟` and `ℬ` are isomorphic away from `v`, `σ₁` and their conjugates, and
the definition of `K(N, m)` via an identification `GG(A_f^p) ≅ GJ(A_f^p)`,
read in the original. Taking the identification as induced by an isomorphism
of algebras with involution over `A_f^p`, and the topological packaging, are
implementation choices; `pointsHomeomorphOfEquiv` is a generic internal
helper.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies: the published `Langlands.Shimura.Unitary.HarrisSplitPrimeLevels`
(with `HarrisSplitTower`, `PointsSplit`, `Global.PrimeToFiniteAdeles`), the
published `Langlands.Shimura.Unitary.InvolutionBaseChangeTower`
(`similitudesEquiv`), `PEL.TraceSimilitudesLevels` (`transport`,
`transportFunctor`), and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`
under Lean 4.34.0, in particular `IsModuleTopology.continuous_of_linearMap`,
`Continuous.units_map` and `Functor.isoWhiskerLeft`.
