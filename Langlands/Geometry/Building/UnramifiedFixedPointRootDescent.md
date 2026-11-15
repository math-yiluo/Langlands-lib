# Fixed-point descent and unit cocharacter points over a Galois extension

Module `Langlands.Geometry.Building.UnramifiedFixedPointRootDescent`.

This module provides two auxiliary facts for the descent of zero-value root jumps from
`K = F^ur = inertiaFixedField F` to `F`. That descent is used for
`UnramifiedZeroJumpDescentStatement`. The module contains no `def` and no new statement.

- Points of a root group descend. A rational point of `G_K` that every `σ ∈ Aut(K/k)` fixes,
  and that lies in the base change of a root group `U_a`, comes from a rational point of `U_a`.
  This holds for every Galois extension `K/k`, finite or infinite.
- For a unit `c` of valuation one, the cocharacter point `ν_K(c)` lies in the common kernel
  of the character valuations, and its image is the `k`-point `ν(c)`.

The Library already had the first fact for finite Galois extensions:
`GaloisPointComparison.exists_mem_rootGroupPoints_of_fixed` in module
`Langlands.GroupScheme.Rational.OrthogonalOrbitDescent`, which assumes
`[FiniteDimensional k K]`. `F^ur/F` is not finite, so this module proves the general version.

## Results in namespace `Langlands.GroupScheme.GaloisPoint`

Setting. `k ⊆ L` is a field extension and `G` is a group scheme over `Spec k` with affine total
space. `GaloisPoint.coordinates k G L` identifies `L`-points of `G` with `k`-algebra maps
`AffineCoordinateRing k G.X → L`. `GaloisPoint.extend k L G` maps `k`-points to `L`-points.
`GaloisPoint.fixedSubgroup k L G` is the subgroup of `L`-points fixed by every
`σ : L ≃ₐ[k] L`, where `σ` acts by conjugation, that is, by composing coordinates with `σ`
(`coordinates_conjugate`).

- `mem_range_extend_of_fixedField`: assume `hfix`, which says that every element of `L` fixed by
  all `σ : L ≃ₐ[k] L` lies in the image of `k`. Then every `x ∈ fixedSubgroup k L G` is
  `extend k L G y` for some `k`-point `y`.

  Proof. Every coordinate `coordinates k G L x a` is fixed by every `σ`, so by `hfix` it equals
  `algebraMap k L (d a)` for a unique `d a ∈ k`. Since `algebraMap k L` is injective, `d` is a
  `k`-algebra map `AffineCoordinateRing k G.X → k`. Let `y` be the `k`-point with coordinates
  `d`. Then `extend y` has coordinates `algebraMap k L ∘ d` (`coordinates_extend`), which are the
  coordinates of `x`.
- `mem_range_extend_of_isGalois`: the same conclusion when `[IsGalois k L]` holds, with `L/k`
  finite or infinite. Here `hfix` is Mathlib's `InfiniteGalois.mem_range_algebraMap_iff_fixed`.

## Results in namespace `Langlands.GroupScheme.GaloisPointComparison`

Setting. `K/k` is a Galois extension (`[IsGalois k K]`, finite or infinite). `G` is a group
scheme over `Spec k` whose structure morphism is affine (`[IsAffineHom G.X.hom]`).
`rationalConjugate k K G σ` is the action of `σ : K ≃ₐ[k] K` on `G_K(K)`. `rationalExtend k K G`
maps `G(k)` to `G_K(K)`.

- `exists_rationalExtend_eq_of_fixed_of_isGalois`: if a point `g ∈ G_K(K)` satisfies
  `rationalConjugate k K G σ g = g` for every `σ`, then `g = rationalExtend k K G g₀` for some
  `g₀ ∈ G(k)`.

  Proof. `baseChangeCoeffEquiv k K G` identifies `G_K(K)` with the `K`-points of `G`. It sends
  `rationalConjugate` to conjugation (`baseChangeCoeffEquiv_rationalConjugate`), so the image
  of `g` lies in `fixedSubgroup k K G`. By `mem_range_extend_of_isGalois`, that image equals
  `extend y`. Take `g₀ = (rationalCoeffEquiv k G).symm y`. The equation
  `rationalExtend g₀ = g` follows from `baseChangeCoeffEquiv_rationalExtend` and injectivity of
  `baseChangeCoeffEquiv`.
- `exists_mem_rootGroupPoints_of_fixed_of_isGalois`: in addition, let `G` be smooth, let
  `i : S ⟶ G` with `S` a split torus (`IsSplitTorus S.toGrp`), and let `a ≠ 0` be a character
  of `S`. If `g` is fixed by every `σ` and lies in `rootGroupPoints i_K a_K`, then there is
  `g₀ ∈ rootGroupPoints i a` with `rationalExtend k K G g₀ = g`. The previous result gives
  `g₀`. It lies in `U_a(k)` by `rationalExtend_mem_rootGroupPoints_iff` (module
  `RootFunctionFieldRestriction`).

## Results in namespace `Langlands.Geometry.Building`

### Unit cocharacter points

`cocharacterPoints_mem_characterValuationKernel_of_eq_one`: let `A` be a commutative group
scheme over a field `K`, let `v` be a valuation on `K` with values in any linearly ordered
commutative group with zero, let `c ∈ Kˣ` satisfy `v c = 1`, and let `ν` be a cocharacter of
`A`. Then `CocharacterUniformizer.cocharacterPoints K A ν c` lies in
`characterValuationKernel v A.toGrp`. That is, every rational character `χ` of `A` takes a
value of valuation one at this point.

Proof. By `CocharacterUniformizer.rationalCharacterEval_cocharacterPoints`,
`χ(ν(c)) = c ^ ⟨χ, ν⟩`. Its valuation is `(v c) ^ ⟨χ, ν⟩ = 1`.

### The image of `ν_K(c)` as a `k`-point

Setting. `K` is an extension of `k`, `b = algebraBaseMap k K`, `S` is a commutative group
scheme over `Spec k`, and `S_K` is its base change. `G` is a group scheme over `Spec k`.

- `baseChangeCoeffEquiv_cocharacterPoints_baseChange`: for a cocharacter `ν` of `S` and
  `c ∈ Kˣ`, `baseChangeCoeffEquiv k K S.toGrp` sends `cocharacterPoints K S_K ν_K c` to the
  `k`-scheme point `Spec K → S` given by `ν` evaluated at `c`. Here `ν_K` is
  `cocharacterLattice.baseChange b S ν`, and `ν(c)` is the composite of
  `(Gm.affinePointsEquiv _).symm c : Spec K → 𝔾_m` with `ν`.

  Proof. `cocharacterLattice.baseChange_points` rewrites the left side as `ν` composed with the
  `𝔾_m`-point `(Gm.pointsEquiv _ _).symm (Gm.pointsEquiv _ _ ((Gm.affinePointsEquiv 𝟙).symm c))`.
  So it suffices to compare two `𝔾_m`-points through `Gm.pointsEquiv`. Both points correspond to
  the global unit `(Scheme.ΓSpecIso K).inv c` of `Spec K`. A local lemma shows this for any
  `f : Spec R ⟶ T`, using `Gm.affinePointsEquiv_val` and `Iso.hom_inv_id_apply`.
- `exists_mem_characterValuationKernel_baseChangeCoeffEquiv_eq`: let `iS : S ⟶ G`, let `ν` be a
  cocharacter of `S`, let `v` be a valuation on `K`, and let `c ∈ Kˣ` satisfy `v c = 1`. Then
  some `t ∈ characterValuationKernel v S_K` has
  `baseChangeCoeffEquiv k K G (iS_K t) = ν(c) ≫ iS` as `k`-scheme points `Spec K → G`.

  Proof. Take `t = cocharacterPoints K S_K ν_K c`. It lies in the kernel by the first result.
  The image of `iS_K t` is `baseChangeCoeffEquiv k K S.toGrp t ≫ iS`
  (`baseChangeBasePointsEquiv_comp`). The previous lemma identifies this with `ν(c) ≫ iS`.

### Descent from `F^ur` (namespace `MaximalUnramified`)

`exists_mem_rootGroupPoints_of_galoisFixed`: let `F` be a nonarchimedean local field and
`K = inertiaFixedField F`. Let `G` be a smooth group scheme over `Spec F` with affine structure
morphism, `i : S ⟶ G` with `S` a split torus, and `a ≠ 0` a character of `S`. Suppose a point
`g ∈ G_K(K)` is fixed by every `σ : K ≃ₐ[F] K` and lies in `U_{a_K}(K)`. Then
`g = rationalExtend F K G g₀` for some `g₀ ∈ U_a(F)`. This is
`exists_mem_rootGroupPoints_of_fixed_of_isGalois` for the Library instance
`inertiaFixedField_isGalois`.
