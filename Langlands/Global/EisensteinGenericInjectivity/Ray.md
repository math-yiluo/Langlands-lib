# An archimedean ray through a cocharacter

Module `Langlands.Global.EisensteinGenericInjectivity.Ray` defines, for a cocharacter
`c : 𝔾_m → G` over a number field `F`, the ray `s ↦ c(exp s)` in `G(𝔸)`: the image under `c` of
the adelic point of `𝔾_m` equal to `exp s` at every infinite place and to `1` at every finite
place. It computes the ray in a representation that diagonalizes `c`, and proves that the ray is
continuous. The modules `Langlands.Global.EisensteinGenericInjectivity.Separation` and
`Langlands.Global.EisensteinGenericInjectivity.Anchor` move evaluation points along this ray.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`; `σ_w(x) = placeMatrix σ w x`. Complete types are printed by `PrettyPrinter.ppSignature` (the
`#check` form), with the namespaces of the page of
`Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `gmIsAffine`: the underlying scheme of `𝔾_m` over `Spec F` is affine (a local instance of the
  module: it is a pullback of affine schemes).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.gmIsAffine.{u} {F : Type u} [Field F] :
    IsAffine (Gm (Spec ↧F)).X.left
  ```
- `gmRayPoint F s` is the point of `𝔾_m(𝔸)` whose unit is the idele
  `PositiveRealIdeles.full F (expUnit s)`: `exp s` at every infinite place, `1` at every finite
  place.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.gmRayPoint.{u} (F : Type u) [Field F] [NumberField F]
    (s : ℝ) : AdelicGroupPoints F (Gm (Spec ↧F)).toGrp
  ```
- `affineUnitsEquiv_gmRayPoint`: its unit is that idele.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.affineUnitsEquiv_gmRayPoint.{u} {F : Type u} [Field F]
    [NumberField F] (s : ℝ) :
    (Gm.affineUnitsEquiv ↧F ↧(AdeleRing (𝓞 F) F)) (gmRayPoint F s) =
      (PositiveRealIdeles.full F) (PositiveRealTorus.expUnit s)
  ```
- `finite_gmRayPoint`: its finite part is trivial.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.finite_gmRayPoint.{u} {F : Type u} [Field F]
    [NumberField F] (s : ℝ) : (finite F (Gm (Spec ↧F)).toGrp) (gmRayPoint F s) = 1
  ```
- `ray F c s = c(gmRayPoint F s)`, the image under the adelic map of `c`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.ray.{u} (F : Type u) [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} (c : (Gm (Spec ↧F)).toGrp ⟶ G) (s : ℝ) :
    AdelicGroupPoints F G
  ```
- `finite_ray`: the finite part of `ray F c s` is trivial.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.finite_ray.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left] (c : (Gm (Spec ↧F)).toGrp ⟶ G) (s : ℝ) :
    (finite F G) (ray F c s) = 1
  ```
- `ray_zero`: `ray F c 0 = 1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.ray_zero.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} (c : (Gm (Spec ↧F)).toGrp ⟶ G) : ray F c 0 = 1
  ```
- `adelicMatrix_ray`: if `c ≫ σ` is the diagonal cocharacter with weights `e`, then
  `σ(ray F c s)` is the diagonal matrix of the powers `u^{e_i}` of the idele
  `u = PositiveRealIdeles.full F (expUnit s)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.adelicMatrix_ray.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (c : (Gm (Spec ↧F)).toGrp ⟶ G) (e : Fin N → ℤ)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e) (s : ℝ) :
    (adelicMatrix F G σ) (ray F c s) =
      (GeneralLinear.diagonalUnits (AdeleRing (𝓞 F) F) e)
        ((PositiveRealIdeles.full F) (PositiveRealTorus.expUnit s))
  ```
- `placeHom_full_expUnit`: the coordinate of `u` at every infinite place is `exp s`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeHom_full_expUnit.{u} {F : Type u} [Field F]
    [NumberField F] (w : Langlands.Global.InfinitePlace F) (s : ℝ) :
    (placeHom w) ↑((PositiveRealIdeles.full F) (PositiveRealTorus.expUnit s)) = ↑(Real.exp s)
  ```
- `placeMatrix_ray_inv`: under the hypothesis of `adelicMatrix_ray`, at every infinite place
  `σ_w(ray F c s)⁻¹ = diag((exp s)^{−e_i})`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_ray_inv.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (c : (Gm (Spec ↧F)).toGrp ⟶ G) (e : Fin N → ℤ)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (↧F) e)
    (w : Langlands.Global.InfinitePlace F) (s : ℝ) :
    placeMatrix σ w (ray F c s)⁻¹ = Matrix.diagonal fun i => ↑(Real.exp s) ^ (-e i)
  ```
- `continuous_ray`: `s ↦ ray F c s` is continuous on `ℝ`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.continuous_ray.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} (c : (Gm (Spec ↧F)).toGrp ⟶ G) :
    Continuous (ray F c)
  ```

## Proofs

- `adelicMatrix_ray` and `placeMatrix_ray_inv`: the adelic matrix of `c(x)` is the point
  `x ≫ (c ≫ σ)` of `GL_N`, and the Library lemma
  `GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter` (module
  `Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal`) evaluates a diagonal
  cocharacter on a unit. At the place `w`, `placeHom w` maps `u^{−e_i}` to `(exp s)^{−e_i}`.
- `continuous_ray`. The source curve is a positive-real torus point: for `T = 𝔾_m`, `I = PUnit`
  and the splitting `splitTorus.gmIso`,

  `gmRayPoint F s = PositiveRealTorus.continuousFull F PUnit 𝔾_m (splitTorus.gmIso _) (fun _ => expUnit s)`.

  Both sides have the same coordinates under `PositiveRealTorus.coordinates`: on the right by
  `PositiveRealTorus.coordinates_full`, on the left because the coordinate of a point of `𝔾_m`
  through `splitTorus.gmIso` is its unit
  (`GeneralLinear.CocharacterDiagonal.algebraPointsEquiv_comp_gmIso`). The map
  `PositiveRealTorus.continuousFull` (module `Langlands.Global.PositiveRealTorusEmbedding`) is a
  continuous homomorphism and `expUnit` is continuous (`PositiveRealTorus.continuous_expUnit`,
  module `Langlands.Global.PositiveRealTorusLog`), so `s ↦ gmRayPoint F s` is continuous; the
  adelic map `AdelicGroupPoints.map F _ G c` (module
  `Langlands.Global.AdelicGroupNormOneFunctorial`) is a continuous homomorphism.

## Sources

No literature source.
