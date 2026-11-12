# Eichler transformations, reflections and hyperbolic scalings

Module `Langlands.GroupScheme.Quaternionic.EichlerTransformations`.

## Setting

As in `RationalIsometry`: `σ` an involution of the first kind of a division `K`-algebra `D`,
`q` a `σ`-quadratic form on row vectors `D^n` with polar form `h(x, y)`
(`σ.sesqForm (σ.polar q) x y`, linear in `x`, `σ`-semilinear in `y`) and values `q(x)` in
`D` modulo the alternating subspace. Matrices act on row vectors on the right, `v ↦ v M`, so
a product `M₁ * M₂` applies `M₁` first.

## Definitions

* `formRankOne σ q y x`: the matrix of `v ↦ h(v, y) x`.
* `eichlerMatrix σ q e x c`: the **Eichler transformation**
  `E^e_{x,c} : v ↦ v + h(v,e) x - (h(v,x) + h(v,e) c) e`.
  It is admissible when `q(e) = 0`, `h(x, e) = 0` and `[c] = q(x)`.
* `eichlerSet σ q e`: the units equal to an admissible `E^e_{x,c}` (with `h(x,e) = 0`,
  `[c] = q(x)`).
* `reflectionMatrix σ q y c`: the **reflection** `ρ_{y,c} : v ↦ v - h(v,y) c⁻¹ y`,
  admissible for `c ≠ 0` and `[c] = q(y)`; `reflectionSet σ q` collects the admissible ones.
* `scalingMatrix σ q e f a b`: the **hyperbolic scaling**
  `ℓ_{e,f}(a,b) : v ↦ v + h(v,f)(a - 1) e + h(v,e)(b - 1) f`. When
  `h(e,e) = h(f,f) = 0` and `h(e,f) = 1`, it sends `e ↦ a e`, `f ↦ b f` and fixes
  `{e,f}^⊥`. (These polar conditions do not make `(e, f)` a hyperbolic pair of `q` in
  characteristic `2`; preserving `q` additionally needs `q(e) = q(f) = 0`, see below.)

## Results

* `sesqForm_polar_self_of_quadraticValue`: `[c] = q(x)` implies `h(x,x) = c + σ(c)`.
* Eichler transformations: explicit action `vecMul_eichlerMatrix`. `E^e_{x,c}` preserves `h`
  when `h(e,e) = 0`, `h(x,e) = 0` and `h(x,x) = c + σ(c)` (`sesqForm_vecMul_eichlerMatrix`),
  and preserves `q` when it is admissible, i.e. `q(e) = 0`, `h(x,e) = 0` and `[c] = q(x)`
  (`quadraticValue_vecMul_eichlerMatrix`); for `h(e,e) = 0` and `x, y ⊥ e`, composition law
  `E^e_{x,c} E^e_{y,d} = E^e_{x+y, c+d+h(x,y)}` (`eichlerMatrix_mul`); inverse
  `E^e_{-x,σ(c)}`; for singular `e` (`q(e) = 0`), `eichlerSet` consists of rational isometries
  (`eichlerSet_subset`, for linearly ordered `n`), is closed under inverses
  (`inv_mem_eichlerSet`) and contains every admissible matrix (`exists_mem_eichlerSet`);
  rescaling `E^{d e}_{x,c} = E^e_{σ(d) x, σ(d) c d}` (`eichlerMatrix_smul`).
* Reflections: explicit action; admissible reflections (`c ≠ 0`, `[c] = q(y)`) preserve `h`
  and `q` and have inverse `ρ_{y,σ(c)}`;
  `reflectionSet ⊆ rationalIsometryGroup`, closure under inverses, membership.
* Hyperbolic scalings: explicit action (`vecMul_scalingMatrix`).
  * If `h(e,e) = h(f,f) = 0` and `h(e,f) = 1`, then `ℓ(a,b) ℓ(a',b') = ℓ(aa', bb')`
    (`scalingMatrix_mul`).
  * If moreover `a σ(b) = 1`, then `ℓ(a,b)` preserves `h`
    (`sesqForm_vecMul_scalingMatrix`).
  * `ℓ(a,b)` preserves the values of `q` (`quadraticValue_vecMul_scalingMatrix`) when
    `(e, f)` is a hyperbolic pair of `q` (`q(e) = q(f) = 0` and `h(e,f) = 1`) and
    `a σ(b) = 1`. The singularity conditions `q(e) = q(f) = 0` are essential: in
    characteristic `2`, `h(e,e) = 0` does not imply `q(e) = 0`.
* Conjugation (`conj_formRankOne`, `conj_eichlerMatrix`, `conj_reflectionMatrix`,
  `conj_scalingMatrix`): for a unit `g` preserving `h`,
  `g⁻¹ M g` is the matrix of the same kind with all defining vectors replaced by their
  images under `g` (e.g. `g⁻¹ E^e_{x,c} g = E^{eg}_{xg,c}`).
* `map_inv_eq`, `map_ne_zero_of_ne_zero`: `σ` commutes with inversion and preserves
  nonvanishing.

## Provenance

Internal, standard. Eichler transformations (also called Siegel or Eichler–Siegel
transformations) are the classical unipotent isometries attached to a singular vector; in
the hermitian/quadratic-over-division-algebra setting they appear e.g. in Tits's work on
the Kneser–Tits problem and in Rapinchuk's survey of the Kneser–Tits problem as generators
of the elementary subgroup of isometry groups of Witt index one. The formulas here are
written for Tits's σ-quadratic forms with row vectors and are verified directly in Lean;
they are building blocks for the proof of the Kneser–Tits property for quaternionic spin
groups (Task 5398).
