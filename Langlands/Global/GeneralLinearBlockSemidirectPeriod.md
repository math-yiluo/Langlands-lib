# Period reduction on adelic block unipotent subgroups of `GL_n`

This internal module specializes the abstract semidirect period theorem
`Langlands.Global.LeftCosetSpace.Semidirect.integral_fundamentalDomain_eq_zero_of_compact`
to adelic block unipotent subgroups of `GL_n` over a number field `F`. Write
`U_v` for the subgroup functor `blockUnipotent n (CommRingCat.of F) v`
of `groupScheme n (CommRingCat.of F)`. Its matrices `g` have `g i j = δ i j`
whenever `v i ≤ v j`. Two weights `e w : n → ℤ` are compared under
`hw : ∀ i j, e i ≤ e j → w i ≤ w j`, as in
`Langlands.GroupScheme.GeneralLinearBlockLeviProjection`. The adelic points of
`U_e` then split as the normal subgroup of adelic points of `U_w` and the
complement of adelic points of `leviUnipotent n (CommRingCat.of F) e w`.
Everything is in the namespace
`Langlands.Global.GeneralLinearBlockSemidirect`.

## Closedness

- `isClosed_setOf_entries`: over a Hausdorff topological ring, the invertible
  matrices with prescribed entries at prescribed positions form a closed set,
  because each matrix entry is continuous on `GL n A`.
- `isClosed_blockUnipotentSubgroup` and
  `isClosed_blockUnipotentSubgroup_inf_blockLeviSubgroup` are its instances for
  `blockUnipotentSubgroup A e` and for its intersection with
  `blockLeviSubgroup A w`, the matrices with `g i j = 0` whenever `w i ≠ w j`.
- `mem_blockUnipotentSubgroup_of_map`: if the image of `g` under an injective
  coefficient ring homomorphism is `w`-block unipotent, then `g` is.
- `adeleRing_t2Space`: the adele ring of `F` is Hausdorff, as the product of
  the infinite adele ring and the restricted product of the finite completions.
- `isClosed_adelicPoints_ofMatrixSubgroups`: a matrix-subgroup functor whose
  matrix subgroup over the adeles is closed has closed adelic points. The proof
  pulls the closed set back along the continuous `affinePointsEquiv`.
- `isClosed_adelicPoints_blockUnipotent` and
  `isClosed_adelicPoints_leviUnipotent` apply it to `U_e` and to
  `leviUnipotent n (CommRingCat.of F) e w`.

## The semidirect data

- `normalInclusion F hw` is the inclusion of the adelic points of `U_w` into
  those of `U_e`, and `leviInclusion F e w` is the inclusion of the adelic
  points of `leviUnipotent n (CommRingCat.of F) e w`.
- `leviProjection F hw` is `pointsLeviProjection` over the adele ring.
- `leviProjection_leviInclusion`, `exists_normalInclusion_eq` and
  `leviProjection_normalInclusion` state that the projection retracts the Levi
  inclusion and that its kernel is the image of `normalInclusion F hw`.
- `isEmbedding_normalInclusion`, `continuous_leviInclusion` and
  `continuous_leviProjection` give the topological hypotheses.
- `leviInclusion_mem_rationalSubgroup` and
  `leviProjection_mem_rationalSubgroup`: both maps send rational points to
  rational points. The second uses `pointsLeviProjection_naturality` along the
  inclusion `F → 𝔸_F`.
- `normalInclusion_mem_rationalSubgroup_iff`: an adelic point of `U_w` is
  rational in `U_e` iff it is rational in `U_w`. For the forward direction, the
  rational point of `U_e` has the same matrix over `𝔸_F` as the given point.
  Its matrix over `F` is therefore `w`-block unipotent by
  `affinePointsEquiv_naturality` and `mem_blockUnipotentSubgroup_of_map`,
  because `F → 𝔸_F` is injective.

## Compactness

`leviRationalQuotientCompactSpace`: if the rational quotient of `U_e` is
compact, then so is the rational quotient of
`leviUnipotent n (CommRingCat.of F) e w`. The projection descends to a
continuous map between the left coset spaces. It is surjective because the
projection retracts the Levi inclusion, so the image of the compact quotient is
the whole quotient.

`thresholdRationalQuotientCompactSpace`: for `e : Fin m → ℤ` and `c : ℤ`,
assuming `CompactSpace (AdeleQuotient F)`, the rational quotient of
`blockUnipotent (Fin m) (CommRingCat.of F) (thresholdWeight e c)` is compact.
The proof renumbers the threshold weight into a standard two-block weight with
`exists_perm_thresholdWeight_eq_twoBlockWeight`. It then rewrites the subgroup
functor as an inverse image under permutation conjugation
(`blockUnipotent_eq_comap_innerIso_permPoint`). Finally it transports the
published compactness of the standard two-block quotient
(`GeneralLinearBlockUnipotent.rationalQuotientCompactSpace`) with
`rationalQuotientCompactSpace_comap`.

## The period theorem

`integral_fundamentalDomain_eq_zero`: assume the rational quotients of `U_e`
and `U_w` are compact. Let `φ` be a continuous complex function on the adelic
points of `U_e` that is invariant under left multiplication by rational points.
Suppose that for every adelic point `m` of
`leviUnipotent n (CommRingCat.of F) e w`, the integral of
`y ↦ φ (normalInclusion F hw y * leviInclusion F e w m)` over the
fundamental domain of the rational points of `U_w`, against Haar measure, is
zero. Then the integral of `φ` over the fundamental domain of the rational
points of `U_e`, against Haar measure, is zero. The proof derives compactness of
the Levi quotient from `leviRationalQuotientCompactSpace` and applies the
abstract theorem to the data above.

## Provenance

The module is internal. It assembles published closedness, compactness and
point-functor results with the abstract semidirect period theorem of
`Langlands.Global.LeftCosetSemidirectPeriod`, and with the block Levi
projection and permutation conjugation modules. Block unipotent radicals of
`GL_n` decompose as semidirect products of a normal block unipotent subgroup
and a Levi part, which is standard; no other literature theorem is invoked.
The integrals are over the fundamental domains of
`LeftCosetSpace.fundamentalDomain`, not over the normalized quotient measure.
