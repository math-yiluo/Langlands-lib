# Divisibility of functions on smooth schemes

Module `Langlands.GroupScheme.IntegralModel.Smoothening.SmoothSections`. This is
a helper module of the proof of
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`.

The universal property of the smoothening needs one fact about an arbitrary
smooth scheme `Y` over a strictly Henselian discrete valuation ring `R`. Let `c`
be a global function on `Y` and `s ≠ 0` an element of `R`. If `s` divides `χ c`
for every `R`-algebra map `χ` from the global functions of `Y` to `R`, then
`c = s • c'` for a global function `c'`. The module proves this in three steps.
First, on a smooth `R`-algebra the values at `R`-points detect the maximal ideal
(Nullstellensatz and Hensel's lemma). Next, this gives the divisibility on every
affine open. Finally, the local quotients glue because `s` is a
non-zero-divisor on the functions of every open set (flatness). The argument is
internal to this project. It is the standard argument showing that sections of a
smooth scheme over a strictly Henselian base are dense in the special fibre.

## Nullstellensatz

`exists_algHom_ne_zero_of_isReduced`: let `k` be an algebraically closed field
and `D` a reduced finitely generated `k`-algebra. Every `r ≠ 0` in `D` has a
`k`-algebra map `φ : D →ₐ[k] k` with `φ r ≠ 0`.

Proof: `D` is a Jacobson ring (`isJacobsonRing_of_finiteType`), so the Jacobson
radical of `⊥` is `⊥` (`IsJacobsonRing.out'`, `⊥` is radical because `D` is
reduced). Hence `r` lies outside some maximal ideal `m`. The Library map
`pointOfMaximal k m : D →ₐ[k] k` has kernel `m`
(`pointOfMaximal_eq_zero_iff`), so it does not vanish at `r`.

## Hensel

`detectsMaximal_of_smooth`: let `R` be a Henselian local ring with algebraically
closed residue field `k`, and `C` a smooth `R`-algebra. Then the family of
`R`-algebra maps `χ : C →ₐ[R] R` has the `DetectsMaximal` property of the
`TensorDensity` module: if `χ c` lies in the maximal ideal of `R` for every `χ`,
then `c` lies in `𝔪 C`.

Proof: by `one_tmul_eq_zero_iff` it suffices to show `1 ⊗ c = 0` in
`k ⊗[R] C`. Suppose not. The algebra `k ⊗[R] C` is smooth over the field `k`, so
it is reduced (Library `SmoothReducedProof.isReduced_of_smooth_of_domain`). It is
finitely generated over `k`. The Nullstellensatz step gives `φ` with
`φ (1 ⊗ c) ≠ 0`. The composite `C → k ⊗[R] C → k` lifts to an `R`-point
`σ : C →ₐ[R] R` (Library `HenselianSections.exists_lift_of_smooth`, the residue
map of `R` being surjective). So `φ (1 ⊗ c)` is the residue of `σ c`. This
residue is zero because `σ c` lies in the maximal ideal, a contradiction.

`exists_eq_smul_of_smooth_algebra`: if moreover `R` is a discrete valuation
ring, `C : Type u` is a smooth `R`-algebra, `s ≠ 0` in `R` and `s` divides
`χ c` for every `R`-algebra map `χ : C →ₐ[R] R`, then `c = s • c'` for some
`c' : C`. This is `DetectsMaximal.exists_eq_smul` (module `TensorDensity`)
applied to `detectsMaximal_of_smooth C`.

## Gluing on a scheme

Let `X` be a scheme. `topRes U : Γ(X, ⊤) ⟶ Γ(X, U)` is the restriction of global
functions to an open set `U`.

- `map_topRes`: restriction from `U` to `V ≤ U` after `topRes U` is `topRes V`.
- `topRes_top`: `topRes ⊤` is the identity.
- `eq_zero_of_mul_eq_zero`: let `σ` be a global function such that
  multiplication by `σ` is injective on `Γ(X, U)` for every affine open `U`.
  Then for every open `W`, `topRes W σ * t = 0` implies `t = 0`. Indeed, the
  affine opens contained in `W` cover `W` (affine opens form a basis,
  `isBasis_affineOpens`). The restriction of `t` to each of them is zero, so
  `t = 0` by the sheaf property (`eq_of_locally_eq'`).
- `exists_eq_mul_of_affine`: let `σ` be as above and `c` a global function.
  Suppose that on every affine open `U` the restriction of `c` is
  `topRes U σ * t U` for some `t U`. Then `c = σ * c'` for a global function
  `c'`. On `U ⊓ V`, both restrictions of `t U` and `t V`, multiplied by `σ`, give
  the restriction of `c`. By the previous lemma they agree. So the family `t` is
  compatible and glues to `c'` (`existsUnique_gluing'`, using
  `iSup_affineOpens_eq_top`). Then `c` and `σ * c'` agree on every affine open,
  so they are equal (`eq_of_locally_eq'`).

## Schemes over `Spec R`

Let `R` be a commutative ring and `Y` an object of `Over (Spec R)`. Its global
functions form the `R`-algebra `((algΓ R).obj Y).unop` (Mathlib's `algΓ`).

- `openAlgebra Y U`: the `R`-algebra structure on `Γ(Y.left, U)` obtained by
  composing `algebraMap` with `topRes U`. `topResAlgHom Y U` is `topRes U` as an
  `R`-algebra map.
- `smooth_openAlgebra`: if `Y.hom` is smooth and `U` is an affine open, then
  `Γ(Y.left, U)` is a smooth `R`-algebra. `HasRingHomProperty.appLE` gives a
  smooth ring map `Γ(Spec R, ⊤) → Γ(Y.left, U)`. Precompose it with the
  isomorphism `(ΓSpecIso R).inv`, which is smooth because it is bijective.
- `flat_openAlgebra`: the same with flat in place of smooth.

From now on `R` is a domain.

- `eq_zero_of_algebraMap_mul_eq_zero`: if `Y.hom` is flat, `s ≠ 0`, `W` is open
  and `t ∈ Γ(Y.left, W)` satisfies `(image of s) * t = 0`, then `t = 0`. By
  `eq_zero_of_mul_eq_zero` it suffices to treat affine `W`. There the product is
  `s • t` in the flat, hence torsion-free, `R`-module `Γ(Y.left, W)`.
- `isTorsionFree_sections` (instance): if `Y.hom` is flat, the global functions
  form a torsion-free `R`-module. This is the case `W = ⊤`.
- `flat_sections` (instance): if moreover `R` is a discrete valuation ring, the
  global functions form a flat `R`-module. The proof is instance search: Mathlib
  knows that torsion-free modules over a discrete valuation ring are flat.
- `exists_eq_smul_of_smooth`: let `R` be a Henselian discrete valuation ring with
  algebraically closed residue field and `Y.hom` smooth. Let `s ≠ 0` and `c` be a
  global function such that `s ∣ χ c` for every `R`-algebra map `χ` from the
  global functions to `R`. Then `c = s • c'` for some global function `c'`.
  On an affine open `U`, the algebra `Γ(Y.left, U)` is smooth. Every `R`-point
  `χ` of it gives the `R`-point `χ ∘ topResAlgHom` of the global functions, so
  `s` divides `χ (topRes U c)`. The `DetectsMaximal` property of
  `detectsMaximal_of_smooth` then gives `topRes U c = s • t`
  (`DetectsMaximal.exists_eq_smul`). Glue with `exists_eq_mul_of_affine`.
  Multiplication by the image of `s` is injective on affine opens by
  `eq_zero_of_algebraMap_mul_eq_zero`.

## Library and Mathlib results used

- Library: `P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed.pointOfMaximal`
  and `pointOfMaximal_eq_zero_iff`,
  `Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain`,
  `Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_smooth`.
- Mathlib: `isJacobsonRing_of_finiteType`, `IsJacobsonRing.out'`,
  `Opens.isBasis_iff_nbhd`, `isBasis_affineOpens`, `iSup_affineOpens_eq_top`,
  `TopCat.Sheaf.eq_of_locally_eq'`, `TopCat.Sheaf.existsUnique_gluing'`,
  `HasRingHomProperty.appLE`, `RingHom.Smooth.of_bijective`,
  `RingHom.Flat.of_bijective`, `RingHom.smooth_algebraMap`,
  `RingHom.flat_algebraMap_iff`, `algΓ`.
