# Constant charts of an abelian scheme across an Artinian extension

Module `Langlands.AbelianScheme.ArtinianConstantCharts` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts`).

## The setting

`Setting R' R` bundles a surjection `φ : R' → R` of rings with `R'` local, a coefficient field
`σ : k → R'` of `R'` (`k` the residue field of `R'`, with `residue ∘ σ = id`) and the induced map
`ψ : R → k` with `ψ ∘ φ = residue`. `Setting.exists` constructs one for every surjection with
kernel in the maximal ideal when `R'` is Artinian and contains `ℚ`, using the coefficient field of
`RingTheory.exists_coefficientField` (module `ArtinianCharZeroCoefficientField`). Write
`t = Spec φ` (the closed immersion `Spec R ⟶ Spec R'` induced by `φ`), `c = Spec ψ` and
`sσ = Spec σ`; `c_t_sσ` says `c ≫ t ≫ sσ = 𝟙`. Apart from the hypothesis of `Setting.exists`,
this module uses no condition relating `ker φ` to the maximal ideal of `R'`; the elementary
condition `maximalIdeal R' * ker φ = 0` is needed only for the correction of transition maps.

## The constant model of an abelian scheme

For an abelian scheme `B` over `Spec R`:

- `A₀` is its special fibre, the base change along `c`, an abelian variety over `k`, with the
  inclusion `jB : A₀ ⟶ B`;
- `C` is the constant abelian scheme `A₀ ×_k R'`, the base change of `A₀` along `sσ`;
- `CS` is the base change of `C` to `Spec R`, with the projection `ρ : CS ⟶ A₀` (a base change of
  `t ≫ sσ`, `isPullback_ρ`) and its section `τ : A₀ ⟶ CS` over `c` (`τ_ρ`, `τ_snd`), which exhibits
  `A₀` as the special fibre of `CS` (`isPullback_τ`). When `R` is local Artinian, `Spec R` has a
  single point (`primeSpectrum_subsingleton`, `c_surjective`), and then on points `τ` is
  surjective (`τ_surjective`, `τ_ρ_apply`) and `ρ` is injective (`ρ_injective`).

## Charts

For an open `U` of `B`, `W U = jB⁻¹ U` is its special fibre and `VT U = ρ⁻¹(W U)` the
corresponding open of `CS`; `a`, `a'` and `w` are the restricted maps, with the special-fibre
squares `isPullback_a` and `isPullback_a'`. For affine `U`, `exists_chartIso` gives an isomorphism
`VT U ≅ U` over `Spec R` that is the identity on the special fibre `W U`, when `R'` is Artinian.
Both are smooth affine deformations of the same affine smooth `k`-scheme along the nilpotent
surjection `ψ`, and the isomorphism comes from `AffineNilpotentThickening.exists_iso_of_fibre`.

`Charts` is a finite affine cover of `B` with such charts `κ i : VT (U i) ⟶ B` (open immersions onto
`U i`, over `Spec R`, equal to `jB` on the special fibre), and `Charts.exists` constructs one for
`R'` Artinian, since `B` is quasi-compact (`exists_finite_affine_cover`). When `R` is local
Artinian, `chart_apply` and `κ_apply` show that on points every chart is `jB ∘ ρ`. Consequently,
for such `R`, the charts glue to `CS` on the level of points, and `lift`, `θS` give the transition
maps `θS i j : VT (U i) ⊓ VT (U j) ⟶ CS`, which fix points
(`θS_pointwise`), are the inclusions on the diagonal (`θS_self`), satisfy the cocycle condition
(`θS_cocycle`) and form the gluing datum `transitionData` of `TwistedOpenGluing`.

## Provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis revised
14 March 2021, computes the obstruction to lifting an abelian scheme from smooth lifts of the
members of an affine cover (proof of Proposition 2.2.4.1, printed pp. 152–154, PDF pp. 180–182;
the obstruction theory is Definition 2.1.2.1 and Proposition 2.1.2.2, printed p. 114, PDF p. 142).
SGA 1, Exposé III, Théorème 4.1 and Lemme 4.2 (recomposed edition, arXiv math/0206203v2, printed
p. 58, PDF p. 74) give local existence of smooth lifts and their local uniqueness up to isomorphism.
This module specializes that choice: when `R'` has a coefficient field, as a local Artinian
`ℚ`-algebra does, the constant abelian scheme `C` is a smooth lift of the special fibre, and the
affine comparison `exists_chartIso` (the affine case of the local uniqueness, proved with
`AffineNilpotentThickening.exists_iso_of_fibre`) lets every local lift be taken as an open of the
common model `C`. Over a general Artinian base such a common constant model need not exist.
