# The limit homomorphism and `P(λ) ≅ U(λ) ⋊ Z(λ)` for separated group schemes

This module concerns the dynamic subgroup functors `P_G(λ)`, `Z_G(λ)` and `U_G(λ)` of
`Langlands.GroupScheme.Dynamic.Basic`. Here `λ : 𝔾_{m,S} ⟶ G` is a cocharacter of a group
scheme `G` over an arbitrary base scheme `S`. For `G` with separated structure morphism
(`[IsSeparated G.X.hom]`), the module proves the following on the points over every test scheme
`T` over `S`.

1. Taking the limit at zero of the conjugation orbit is a group homomorphism
   `P_G(λ)(T) →* Z_G(λ)(T)`, natural in `T`.
2. Its kernel is `U_G(λ)(T)`.
3. It is the identity on `Z_G(λ)(T)`, so the inclusion `Z_G(λ)(T) ≤ P_G(λ)(T)` is a section.
4. Multiplication `(u, z) ↦ u * z` is a group isomorphism from the semidirect product
   `U_G(λ)(T) ⋊ Z_G(λ)(T)` onto `P_G(λ)(T)`. In the semidirect product, `Z_G(λ)(T)` acts on
   `U_G(λ)(T)` by conjugation.

Nothing is assumed of `G` besides separatedness: no affineness and no finite presentation. Test
schemes are arbitrary, so non-reduced and non-flat ones are included. The module is about
points. It does not prove that `P_G(λ)`, `Z_G(λ)` or `U_G(λ)` is representable, so it gives no
morphism of schemes `P_G(λ) ⟶ Z_G(λ)`.

## Sources

- Conrad, Gabber, Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), Lemma 2.1.5, proof
  (printed p. 50, PDF p. 76). The proof shows that `g ↦ lim_{t→0} t.g` is a multiplicative map
  `P_G(λ) → G`: "Such a map is necessarily a k-group homomorphism, and its scheme-theoretic
  kernel is exactly the desired `U_G(λ)`."
- The same book, Proposition 2.1.8(2) (printed p. 53, PDF p. 79): "The multiplication map
  `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an isomorphism of k-groups." Proof, Step 2 (printed p. 54, PDF
  p. 80): the limit homomorphism "is a projector onto the k-subgroup `Z_G(λ)`, from which the
  desired semidirect product decomposition is immediate."

CGP work with an affine group of finite presentation over a ring `k`, with points valued in
`k`-algebras, and prove these as statements about `k`-group schemes. This module proves the
same group-theoretic statements on `T`-valued points, for every scheme `T` over `S`. It needs
only separatedness of `G`, which gives unique limits that lie in `Z_G(λ)` (the published module
`Langlands.GroupScheme.Dynamic.Uniqueness`). CGP write the semidirect product as
`Z_G(λ) ⋉ U_G(λ)`. Mathlib's `N ⋊[φ] H` puts the normal factor first, so here it is
`U_G(λ)(T) ⋊ Z_G(λ)(T)`, with multiplication `(u, z) ↦ u * z`.

## Without separatedness

These hold for every group scheme `G` over `S`.

- `Dynamic.HasLimit.comp`: if `l` is a limit of `g : T ⟶ G` and `a : T' ⟶ T`, then `a ≫ l` is
  a limit of `a ≫ g`. The extension is restricted along `a × 𝔸¹`, using the published
  `IsOrbitExtension.whiskerRight` and `evalZero_whiskerRight`.
- `Dynamic.limit g`, for `g` in `P_G(λ)(T)`, is a limit of `g` chosen by `Classical.choice` from
  the published `exists_hasLimit` (module `Langlands.GroupScheme.Dynamic.Decomposition`).
  `hasLimit_limit` says it is a limit. For separated `G` the limit is unique, so the choice does
  not matter (`limit_eq`).
- `Dynamic.centralizer_le_normalizer_unipotent`: `Z_G(λ)(T)` lies in the normalizer of
  `U_G(λ)(T)` in the group `G(T)` of all points. This is the published `conj_mem_unipotent`,
  applied to `z` and to `z⁻¹`, which both lie in `P_G(λ)(T)`.
- `Dynamic.centralizerConj T : Z_G(λ)(T) →* MulAut (U_G(λ)(T))` is the conjugation action. It is
  Mathlib's `Subgroup.normalizerMonoidHom` composed with the inclusion of the previous item.
  `centralizerConj_apply_coe` says that `z` acts by `u ↦ z * u * z⁻¹`.
- `Dynamic.mul_mem_parabolic`: `u * z` lies in `P_G(λ)(T)` for `u` in `U_G(λ)(T)` and `z` in
  `Z_G(λ)(T)`.

## The limit homomorphism

From here on `G.X.hom` is separated.

- `Dynamic.limit_eq`: if `l` is a limit of `g`, then `limit g = l`. This is the published
  `HasLimit.unique`.
- `Dynamic.limit_mem_centralizer`: `limit g` lies in `Z_G(λ)(T)`. This is the published
  `HasLimit.mem_centralizer`.
- `Dynamic.limitHom T : P_G(λ)(T) →* Z_G(λ)(T)` sends `g` to `limit g`
  (`limitHom_apply_coe`). It preserves `1` because `1` is its own limit, and it is
  multiplicative by the published `HasLimit.mul` together with `limit_eq`.
- `Dynamic.hasLimit_iff_limitHom`: `g` has limit `l` exactly when `g` lies in `P_G(λ)(T)` and
  `limitHom T g = l`.
- `Dynamic.limitHom_comp`: naturality. For `a : T' ⟶ T` and `g` in `P_G(λ)(T)`, the limit of
  `a ≫ g` is `a ≫ limitHom T g`. This follows from `HasLimit.comp` and `limit_eq`.
- `Dynamic.limitHom_inclusion` and `limitHom_comp_inclusion`: `limitHom T` is the identity on
  `Z_G(λ)(T)`, since a point of `Z_G(λ)` is its own limit (the published
  `hasLimit_of_mem_centralizer`). In particular `limitHom T` is surjective
  (`limitHom_surjective`).
- `Dynamic.ker_limitHom`: the kernel of `limitHom T` is `U_G(λ)(T)`, as a subgroup of
  `P_G(λ)(T)`. By definition `U_G(λ)(T)` consists of the points with limit `1`.
  `Dynamic.limit_eq_one_iff` states the same for a single point.

## The semidirect product decomposition

- `Dynamic.isComplement'_unipotent_centralizer_of_isSeparated`: `U_G(λ)(T)` and `Z_G(λ)(T)` are
  complementary subgroups of `P_G(λ)(T)`. This is the published
  `isComplement'_unipotent_centralizer`. Its two hypotheses, uniqueness of limits and limits in
  `Z_G(λ)`, are supplied by `HasLimit.unique` and `HasLimit.mem_centralizer`.
- `Dynamic.mul_inv_limit_mem_unipotent`: for `g` in `P_G(λ)(T)`, the point `g * (limit g)⁻¹`
  has limit `limit g * (limit g)⁻¹ = 1`, so it lies in `U_G(λ)(T)`.
- `Dynamic.limit_mul`: for `u` in `U_G(λ)(T)` and `z` in `Z_G(λ)(T)`, the limit of `u * z` is
  `1 * z = z`.
- `Dynamic.semidirectEquiv T`: the group isomorphism
  `U_G(λ)(T) ⋊[centralizerConj T] Z_G(λ)(T) ≃* P_G(λ)(T)`, `(u, z) ↦ u * z`. Its inverse is
  `g ↦ (g * (limit g)⁻¹, limit g)`. It is multiplicative because the product in the semidirect
  product is `(u, z) (u', z') = (u * (z * u' * z⁻¹), z * z')`. The inverse is a left inverse by
  `limit_mul`. `semidirectEquiv_apply_coe`, `semidirectEquiv_symm_apply_left_coe` and
  `semidirectEquiv_symm_apply_right` give its values.
- `Dynamic.limitHom_comp_semidirectEquiv`: under this isomorphism, the limit homomorphism is
  the projection `SemidirectProduct.rightHom` onto `Z_G(λ)(T)`.

For diagonal cocharacters of `GL_n` over a ring, the published module
`Langlands.GroupScheme.Dynamic.GeneralLinearOrbit` computes the limit explicitly as the block
diagonal part of a block upper triangular matrix. This module does not restate that computation
in terms of `limitHom`.
